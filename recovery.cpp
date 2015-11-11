/*
 * Copyright (C) 2007 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <linux/fs.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "bootloader.h"
#include "common.h"
#include "cutils/properties.h"
#include "cutils/android_reboot.h"
#include "install.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "make_ext4fs.h"
#include "roots.h"
#include "ui.h"
#include "charge_ui.h"
#include "screen_ui.h"
#include "device.h"
#include "adb_install.h"
#include "lock_passwd.h"
#include "meizu/meizu_common.h"
extern "C" {
#include "minadbd/adb.h"
}

#include "meizu/version.h"
#include "meizu/boot_mode.h"
#include "meizu/backlight.h"

enum WipeDataType {
	WIPE_NONE,
	WIPE_SDCARD,
	WIPE_USERDATA,
	WIPE_ALL,
	WIPE_EXTERNAL_SDCARD,
};

#define BACKLIGHT_BRIGHTNESS	(68)
#define MAX_PWD_ERR_NUM         (5)
#define PWD_ERR_TIMEOUT                 (60)

struct partition {
	unsigned char boot_ind;		/* 0x80 - active */
	unsigned char head;			/* starting head */
	unsigned char sector;		/* starting sector */
	unsigned char cyl;			/* starting cylinder */
	unsigned char sys_ind;		/* What partition type */
	unsigned char end_head;		/* end head */
	unsigned char end_sector;	/* end sector */
	unsigned char end_cyl;		/* end cylinder */
	unsigned int start_sect;	/* starting sector counting from 0 */
	unsigned int nr_sects;		/* nr of sectors in partition */
} __attribute__((packed));

struct legacy_mbr {
    unsigned char boot_code[440];
    unsigned int unique_mbr_signature;
    unsigned short unknown;
    struct partition partition_record[4];
    unsigned short signature;
} __attribute__((packed));

struct selabel_handle *sehandle;

static const struct option OPTIONS[] = {
  { "send_intent", required_argument, NULL, 's' },
  { "update_package", optional_argument, NULL, 'u' },
  { "update_package_wipe", no_argument, NULL, 'U' },
  { "wipe_userdata", no_argument, NULL, 'w' },
  { "wipe_cache", no_argument, NULL, 'c' },
  { "wipe_sdcard", no_argument, NULL, 'd' },
  { "wipe_all", no_argument, NULL, 'a' },
  { "partition", no_argument, NULL, 'P' },
  { "show_text", no_argument, NULL, 't' },
  { "just_exit", no_argument, NULL, 'x' },
  { "locale", required_argument, NULL, 'l' },
  { "stages", required_argument, NULL, 'g' },
   { "wipe_sdcard1", no_argument, NULL, 'D' },
  { NULL, 0, NULL, 0 },
};

#define LAST_LOG_FILE "/cache/recovery/last_log"
#define UPDATE_LOCATE_FILE "/cache/.update_locate"

static const char *CACHE_LOG_DIR = "/cache/recovery";
static const char *COMMAND_FILE = "/cache/recovery/command";
static const char *INTENT_FILE = "/cache/recovery/intent";
static const char *LOG_FILE = "/cache/recovery/log";
static const char *LAST_INSTALL_FILE = "/cache/recovery/last_install";
static const char *LOCALE_FILE = "/cache/recovery/last_locale";
static const char *CACHE_ROOT = "/cache";
static const char *SDCARD_ROOT = "/sdcard";
static const char *TEMPORARY_LOG_FILE = "/tmp/recovery.log";
static const char *TEMPORARY_INSTALL_FILE = "/tmp/last_install";

ScreenRecoveryUI* ui = NULL;
char* locale = NULL;
char* stage = NULL;

int bootmode;

static time_t last_wakeup_key_time;

static pthread_mutex_t gKeyMutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t gKeyCond = PTHREAD_COND_INITIALIZER;

static void update_and_wipe(bool is_update, enum WipeDataType wipe_type);

extern bool is_system_locked(void);
extern int get_update_package_path(char *path_out, int path_len);
#ifdef MEIZU_MX2
extern int get_update_package_path_mx2(char *path_out, int path_len);
extern void do_repartition(void);
#endif



/*
 * The recovery tool communicates with the main system through /cache files.
 *   /cache/recovery/command - INPUT - command line for tool, one arg per line
 *   /cache/recovery/log - OUTPUT - combined log file from recovery run(s)
 *   /cache/recovery/intent - OUTPUT - intent that was passed in
 *
 * The arguments which may be supplied in the recovery.command file:
 *   --send_intent=anystring - write the text out to recovery.intent
 *   --update_package=path - verify install an OTA package file
 *   --wipe_data - erase user data (and cache), then reboot
 *   --wipe_cache - wipe cache (but not user data), then reboot
 *   --set_encrypted_filesystem=on|off - enables / diasables encrypted fs
 *   --just_exit - do nothing; exit and reboot
 *
 * After completing, we remove /cache/recovery/command and reboot.
 * Arguments may also be supplied in the bootloader control block (BCB).
 * These important scenarios must be safely restartable at any point:
 *
 * FACTORY RESET
 * 1. user selects "factory reset"
 * 2. main system writes "--wipe_data" to /cache/recovery/command
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--wipe_data"
 *    -- after this, rebooting will restart the erase --
 * 5. erase_volume() reformats /data
 * 6. erase_volume() reformats /cache
 * 7. finish_recovery() erases BCB
 *    -- after this, rebooting will restart the main system --
 * 8. main() calls reboot() to boot main system
 *
 * OTA INSTALL
 * 1. main system downloads OTA package to /cache/some-filename.zip
 * 2. main system writes "--update_package=/cache/some-filename.zip"
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--update_package=..."
 *    -- after this, rebooting will attempt to reinstall the update --
 * 5. install_package() attempts to install the update
 *    NOTE: the package install must itself be restartable from any point
 * 6. finish_recovery() erases BCB
 *    -- after this, rebooting will (try to) restart the main system --
 * 7. ** if install failed **
 *    7a. prompt_and_wait() shows an error icon and waits for the user
 *    7b; the user reboots (pulling the battery, etc) into the main system
 * 8. main() calls maybe_install_firmware_update()
 *    ** if the update contained radio/hboot firmware **:
 *    8a. m_i_f_u() writes BCB with "boot-recovery" and "--wipe_cache"
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8b. m_i_f_u() writes firmware image into raw cache partition
 *    8c. m_i_f_u() writes BCB with "update-radio/hboot" and "--wipe_cache"
 *        -- after this, rebooting will attempt to reinstall firmware --
 *    8d. bootloader tries to flash firmware
 *    8e. bootloader writes BCB with "boot-recovery" (keeping "--wipe_cache")
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8f. erase_volume() reformats /cache
 *    8g. finish_recovery() erases BCB
 *        -- after this, rebooting will (try to) restart the main system --
 * 9. main() calls reboot() to boot main system
 */

static const int MAX_ARG_LENGTH = 4096;
static const int MAX_ARGS = 100;

// open a given path, mounting partitions as necessary
FILE*
fopen_path(const char *path, const char *mode) {
    if (ensure_path_mounted(path) != 0) {
        LOGE("Can't mount %s\n", path);
        return NULL;
    }

    // When writing, try to create the containing directory, if necessary.
    // Use generous permissions, the system (init.rc) will reset them.
    if (strchr("wa", mode[0])) dirCreateHierarchy(path, 0777, NULL, 1, sehandle);

    FILE *fp = fopen(path, mode);
    return fp;
}

// close a file, log an error if the error indicator is set
static void
check_and_fclose(FILE *fp, const char *name) {
    fflush(fp);
    if (ferror(fp)) LOGE("Error in %s\n(%s)\n", name, strerror(errno));
    fclose(fp);
}

// command line args come from, in decreasing precedence:
//   - the actual command line
//   - the bootloader control block (one per line, after "recovery")
//   - the contents of COMMAND_FILE (one per line)
static void
get_args(int *argc, char ***argv) {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    get_bootloader_message(&boot);  // this may fail, leaving a zeroed structure
    stage = strndup(boot.stage, sizeof(boot.stage));

    if (boot.command[0] != 0 && boot.command[0] != 255) {
        LOGI("Boot command: %.*s\n", sizeof(boot.command), boot.command);
    }

    if (boot.status[0] != 0 && boot.status[0] != 255) {
        LOGI("Boot status: %.*s\n", sizeof(boot.status), boot.status);
    }

    // --- if arguments weren't supplied, look in the bootloader control block
    if (*argc <= 1) {
        boot.recovery[sizeof(boot.recovery) - 1] = '\0';  // Ensure termination
        const char *arg = strtok(boot.recovery, "\n");
        if (arg != NULL && !strcmp(arg, "recovery")) {
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = strdup(arg);
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if ((arg = strtok(NULL, "\n")) == NULL) break;
                (*argv)[*argc] = strdup(arg);
            }
            LOGI("Got arguments from boot message\n");
        } else if (boot.recovery[0] != 0 && boot.recovery[0] != 255) {
            LOGE("Bad boot message\n\"%.20s\"\n", boot.recovery);
        }
    }

    // --- if that doesn't work, try the command file
    if (*argc <= 1) {
        FILE *fp = fopen_path(COMMAND_FILE, "r");
        if (fp != NULL) {
            char *token;
            char *argv0 = (*argv)[0];
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = argv0;  // use the same program name

            char buf[MAX_ARG_LENGTH];
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if (!fgets(buf, sizeof(buf), fp)) break;
                token = strtok(buf, "\r\n");
                if (token != NULL) {
                    (*argv)[*argc] = strdup(token);  // Strip newline.
                } else {
                    --*argc;
                }
            }

            check_and_fclose(fp, COMMAND_FILE);
            LOGI("Got arguments from %s\n", COMMAND_FILE);
        }
    }

    // --> write the arguments we have back into the bootloader control block
    // always boot into recovery after this (until finish_recovery() is called)
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    int i;
    for (i = 1; i < *argc; ++i) {
        strlcat(boot.recovery, (*argv)[i], sizeof(boot.recovery));
        strlcat(boot.recovery, "\n", sizeof(boot.recovery));
    }
	if (*argc > 1) {
		LOGI("Got arguments:\n%s\n", boot.recovery);
		set_bootloader_message(&boot);
	}
}

static void
set_update_bootloader_message(bool is_update, enum WipeDataType wipe_type) {
    struct bootloader_message boot;
	const char *str;

    memset(&boot, 0, sizeof(boot));
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));

	if (is_update) {
		if (wipe_type == WIPE_USERDATA) {
			str = "--update_package_wipe";
		} else {
			str = "--update_package";
		}
	} else {
		switch (wipe_type) {
		case WIPE_SDCARD:
			str = "--wipe_sdcard";
			break;
		case WIPE_USERDATA:
			str = "--wipe_userdata";
			break;
		case WIPE_ALL:
			str = "--wipe_all";
			break;
		default:
			break;
		}
	}

	if (is_update || wipe_type!=WIPE_NONE) {
		strlcat(boot.recovery, str, sizeof(boot.recovery));
	}
	strlcat(boot.recovery, "\n", sizeof(boot.recovery));

    set_bootloader_message(&boot);
}

// How much of the temp log we have copied to the copy in cache.
static long tmplog_offset = 0;

static void
copy_log_file(const char* source, const char* destination, int append) {
    FILE *log = fopen_path(destination, append ? "a" : "w");
    if (log == NULL) {
        LOGE("Can't open %s\n", destination);
    } else {
        FILE *tmplog = fopen(source, "r");
        if (tmplog != NULL) {
            if (append) {
                fseek(tmplog, tmplog_offset, SEEK_SET);  // Since last write
            }
            char buf[4096];
            while (fgets(buf, sizeof(buf), tmplog)) fputs(buf, log);
            if (append) {
                tmplog_offset = ftell(tmplog);
            }
            check_and_fclose(tmplog, source);
        }
        check_and_fclose(log, destination);
    }
}

// Rename last_log -> last_log.1 -> last_log.2 -> ... -> last_log.$max
// Overwrites any existing last_log.$max.
static void
rotate_last_logs(int max) {
    char oldfn[256];
    char newfn[256];

    int i;
    for (i = max-1; i >= 0; --i) {
        snprintf(oldfn, sizeof(oldfn), (i==0) ? LAST_LOG_FILE : (LAST_LOG_FILE ".%d"), i);
        snprintf(newfn, sizeof(newfn), LAST_LOG_FILE ".%d", i+1);
        // ignore errors
        rename(oldfn, newfn);
    }
}

static void
copy_logs() {
    // Copy logs to cache so the system can find out what happened.
    copy_log_file(TEMPORARY_LOG_FILE, LOG_FILE, true);
    copy_log_file(TEMPORARY_LOG_FILE, LAST_LOG_FILE, false);
    copy_log_file(TEMPORARY_INSTALL_FILE, LAST_INSTALL_FILE, false);
    chmod(LOG_FILE, 0600);
    chown(LOG_FILE, 1000, 1000);   // system user
    chmod(LAST_LOG_FILE, 0640);
    chmod(LAST_INSTALL_FILE, 0644);
    chown(LAST_INSTALL_FILE, 1000, 1000);   // system user
    sync();
}

// clear the recovery command and prepare to boot a (hopefully working) system,
// copy our log file to cache as well (for the system to read), and
// record any intent we were asked to communicate back to the system.
// this function is idempotent: call it as many times as you like.
void finish_recovery()
{
	// By this point, we're ready to return to the main system...
	/*
	   if (send_intent != NULL) {
	   FILE *fp = fopen_path(INTENT_FILE, "w");
	   if (fp == NULL) {
	   LOGE("Can't open %s\n", INTENT_FILE);
	   } else {
	   fputs(send_intent, fp);
	   check_and_fclose(fp, INTENT_FILE);
	   }
	   }
	   */
	// Save the locale to cache, so if recovery is next started up
	// without a --locale argument (eg, directly from the bootloader)
	// it will use the last-known locale.
	if (locale != NULL) {
		LOGI("Saving locale \"%s\"\n", locale);
		FILE* fp = fopen_path(LOCALE_FILE, "w");
		fwrite(locale, 1, strlen(locale), fp);
		fflush(fp);
		fsync(fileno(fp));
		check_and_fclose(fp, LOCALE_FILE);
	}

    copy_logs();

    // Reset to normal system boot so recovery won't cycle indefinitely.
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    set_bootloader_message(&boot);

    // Remove the command file, so recovery won't repeat indefinitely.
    if (ensure_path_mounted(COMMAND_FILE) != 0 ||
        (unlink(COMMAND_FILE) && errno != ENOENT)) {
        LOGW("Can't unlink %s\n", COMMAND_FILE);
    }

	unlink(UPDATE_LOCATE_FILE);

    /* ensure all partitions unmounted */
    setup_install_mounts();

    ensure_path_unmounted(CACHE_ROOT);
    sync();  // For good measure.
}

typedef struct _saved_log_file {
    char* name;
    struct stat st;
    unsigned char* data;
    struct _saved_log_file* next;
} saved_log_file;

int
erase_volume(const char *volume) {
    bool is_cache = (strcmp(volume, CACHE_ROOT) == 0);


    saved_log_file* head = NULL;

    if (is_cache) {
        // If we're reformatting /cache, we load any
        // "/cache/recovery/last*" files into memory, so we can restore
        // them after the reformat.

        ensure_path_mounted(volume);

        DIR* d;
        struct dirent* de;
        d = opendir(CACHE_LOG_DIR);
        if (d) {
            char path[PATH_MAX];
            strcpy(path, CACHE_LOG_DIR);
            strcat(path, "/");
            int path_len = strlen(path);
            while ((de = readdir(d)) != NULL) {
                if (strncmp(de->d_name, "last", 4) == 0) {
                    saved_log_file* p = (saved_log_file*) malloc(sizeof(saved_log_file));
                    strcpy(path+path_len, de->d_name);
                    p->name = strdup(path);
                    if (stat(path, &(p->st)) == 0) {
                        // truncate files to 512kb
                        if (p->st.st_size > (1 << 19)) {
                            p->st.st_size = 1 << 19;
                        }
                        p->data = (unsigned char*) malloc(p->st.st_size);
                        FILE* f = fopen(path, "rb");
                        fread(p->data, 1, p->st.st_size, f);
                        fclose(f);
                        p->next = head;
                        head = p;
                    } else {
                        free(p);
                    }
                }
            }
            closedir(d);
        } else {
            if (errno != ENOENT) {
                printf("opendir failed: %s\n", strerror(errno));
            }
        }
    }

    ui->Print("Formatting %s...\n", volume);

    ensure_path_unmounted(volume);
    int result = format_volume(volume);

    if (is_cache) {
        while (head) {
            FILE* f = fopen_path(head->name, "wb");
            if (f) {
                fwrite(head->data, 1, head->st.st_size, f);
                fclose(f);
                chmod(head->name, head->st.st_mode);
                chown(head->name, head->st.st_uid, head->st.st_gid);
            }
            free(head->name);
            free(head->data);
            saved_log_file* temp = head->next;
            free(head);
            head = temp;
        }

        // Any part of the log we'd copied to cache is now gone.
        // Reset the pointer so we copy from the beginning of the temp
        // log.
        tmplog_offset = 0;
        copy_logs();
    }

    return result;
}

static void
print_property(const char *key, const char *name, void *cookie) {
    printf("%s=%s\n", key, name);
}

static void
load_locale_from_cache() {
    FILE* fp = fopen_path(LOCALE_FILE, "r");
    char buffer[80];
    if (fp != NULL) {
        fgets(buffer, sizeof(buffer), fp);
        int j = 0;
        unsigned int i;
        for (i = 0; i < sizeof(buffer) && buffer[i]; ++i) {
            if (!isspace(buffer[i])) {
                buffer[j++] = buffer[i];
            }
        }
        buffer[j] = 0;
        locale = strdup(buffer);
        check_and_fclose(fp, LOCALE_FILE);
    }
}

void reboot_system()
{
	finish_recovery();
	android_reboot(ANDROID_RB_RESTART, 0, 0);
	while(1);
}

static int wipe_sdcard()
{
	LOGI("\n-- Wiping sdcard...\n");
	if (ensure_path_mounted("/data") != 0) {
		LOGE("Can't mount data\n");
		return -1;
	}
	const char *ignore_path[2]={
		".",NULL};
	delete_file("/data/media",ignore_path);
	delete_file("/data/data/com.android.providers.media",ignore_path);
#ifdef MEIZU_MX2
	//erase_volume("/sdcard");
#endif
	LOGI("wipe sdcard complete.\n");
	return 0;
}

static int wipe_ext_sdcard()
{
	const char *ignore_path[2]={".",NULL};

	LOGI("\n-- Wiping external sdcard...\n");
	if (ensure_path_mounted("/storage/sdcard1")) {
		LOGE("Can't mount external sdcard\n");
		return -1;
	}

	delete_file("/storage/sdcard1", ignore_path);
	ensure_path_unmounted("/storage/sdcard1");
	LOGI("wipe external sdcard complete.\n");

	return 0;
}

static int wipe_userdata()
{
	LOGI("\n-- Wiping userdata...\n");
#ifdef MEIZU_MX2
	if (ensure_path_mounted("/data") != 0) {
		LOGE("Can't mount data\n");
		return -1;
	}
	const char *ignore_path[2];
	ignore_path[0] = "/data/media";
	ignore_path[1] = NULL;
	delete_file("/data",ignore_path);
	//erase_volume("/data");
#else
	if (ensure_path_mounted("/data") != 0) {
		LOGE("Can't mount data\n");
		return -1;
	}
	const char *ignore_path[4];
	char key_value[PROPERTY_VALUE_MAX + 1];
	property_get("ro.meizu.customize.demo",key_value,"false");
	LOGI("ro.meizu.customize.demo = %s\n", key_value);
	if(!strcmp(key_value,"false")){
		ignore_path[0] = "/data/media";
		ignore_path[1] = NULL;
	}else{
		ignore_path[0] = "/data/media";
		ignore_path[1] = "/data/misc/wifi/wpa_supplicant.conf";
		ignore_path[2] = "/data/misc/video/volume.conf";
		ignore_path[3] = NULL;
	}
	delete_file("/data",ignore_path);
	erase_volume("/cache");
#endif

#ifdef MEIZU_MX5PRO
	erase_volume("/efs");
#endif

	LOGI("wipe userdata complete.\n");
	return 0;
}
static void wipe_all()
{
	LOGI("\n-- Wiping all...\n");
	erase_volume("/data");
#ifdef MEIZU_MX2
	//erase_volume("/sdcard");
#endif
	erase_volume("/cache");

#ifdef MEIZU_MX5PRO
	erase_volume("/efs");
#endif

	LOGI("wipe all complete.\n");
}

static void do_wipe(enum WipeDataType wipe_type)
{
	switch(wipe_type){
		case WIPE_SDCARD:
			wipe_sdcard();
			break;
		case WIPE_USERDATA:
			wipe_userdata();
			break;
		case WIPE_ALL:
			wipe_all();
			break;
		case WIPE_EXTERNAL_SDCARD:
			wipe_ext_sdcard();
			wipe_all();
			break;
		case WIPE_NONE:
		default:
			break;
	}
}

static int backup_update_package(void)
{
	char path[256] = {0};
	char dst_path[256] = {0};
	char *slash;
	struct stat st;

	LOGI("backup update package...\n");

	ensure_path_mounted("/data");

	/* find the update package */
#ifdef MEIZU_MX2
	if (get_update_package_path_mx2(path, sizeof(path)) != 0) {
#else
	if (get_update_package_path(path, sizeof(path)) != 0) {
#endif
		LOGI("Can't find update package!\n");
		return -1;
	}

	LOGI("Update package is [%s]\n", path);

	if (stat(path, &st)) {
		LOGE("get %s file status error!\n", path);
		return -1;
	}

	/* back update package to /tmp/ */
	slash = strrchr(path, '/');
	snprintf(dst_path, sizeof(dst_path), "/tmp/tmp_%s", slash + 1);

	LOGI("copy %s to %s...\n", path, dst_path);
	easy_cp_func(path, dst_path);

	LOGI("backup update package done.\n");
	return 0;
}

static int restore_update_package(void)
{
	const char *src = NULL, *dst = NULL;

	LOGI("restore update package...\n");

	if (!access("/tmp/tmp_update.bin", F_OK)) {
		src = "/tmp/tmp_update.bin";
		dst = "/data/media/0/update.bin";
	} else if (!access("/tmp/tmp_update.zip", F_OK)) {
		src = "/tmp/tmp_update.zip";
		dst = "/data/media/0/update.zip";
	}

	if (src) {
		LOGI("copy %s to %s...\n", src, dst);

		ensure_path_mounted("/data");
		mkdir("/data/media", 0770);
		mkdir("/data/media/0", 0770);
		chown("/data/media", 1023, 1023);
		chown("/data/media/0", 1023, 1023);

		easy_cp_func(src, dst);
		unlink(src);
	}

	LOGI("restore update package done.\n");
	return 0;
}

static void make_partition(struct partition *p, unsigned int start_sect,
							unsigned int nr_sects)
{
	p->boot_ind		= 0x0;
	p->head			= 0xFE;	// bogus CHS
	p->sector		= 0xFF;
	p->cyl			= 0xFF;
	p->sys_ind		= 0x83;	// linux
	p->end_head		= 0xFE;	// bogus CHS
	p->end_sector	= 0xFF;
	p->end_cyl		= 0xFF;
	p->start_sect	= start_sect;
	p->nr_sects		= nr_sects;
}

static int make_partition_table(void)
{
#ifdef MEIZU_MX2
	#define RESERVED_SIZE		64
	#define PART_IDX_SYSTEM		1
	#define PART_IDX_CACHE		3
	#define PART_IDX_CUSTOM		2
	#define PART_IDX_USERDATA	0
#else
	#define RESERVED_SIZE		192
	#define PART_IDX_SYSTEM		0
	#define PART_IDX_CACHE		1
	#define PART_IDX_CUSTOM		3
	#define PART_IDX_USERDATA	2
#endif

	int fd;
	const char *fname;
	char buf[512] = {0};

	unsigned int start_sect, nr_sects;
	unsigned int userdata_sz;
	unsigned int total_sz;

	struct legacy_mbr old_mbr, mbr;

	fname = "/sys/block/mmcblk0/size";
	fd = open(fname, O_RDONLY);
	if (fd < 0) {
		LOGE("can't open %s: %s\n", fname, strerror(errno));
		return -1;
	}

	/* read eMMC total size */
	read(fd, buf, sizeof(buf) - 1);
	total_sz = strtol(buf, NULL, 10);
	close(fd);

	fname = "/dev/block/mmcblk0";
	fd = open(fname, O_RDWR);
	if (fd < 0) {
		LOGE("can't open %s: %s\n", fname, strerror(errno));
		return -1;
	}

	/* read old the MBR */
	if (read(fd, &old_mbr, sizeof(old_mbr)) != sizeof(old_mbr)) {
		LOGE("read MBR from %s failed: %s", fname, strerror(errno));
		close(fd);
		return -1;
	}
	memcpy(&mbr, &old_mbr, sizeof(mbr));

	/* system */
	start_sect	= (RESERVED_SIZE * 1024 * 1024) / 512;
	nr_sects	= (1536 * 1024 *1024) / 512;
	userdata_sz = total_sz - start_sect - nr_sects;
	make_partition(&mbr.partition_record[PART_IDX_SYSTEM], start_sect, nr_sects);

	/* cache */
	start_sect += nr_sects;
	nr_sects	= (512 * 1024 *1024) / 512;
	userdata_sz = userdata_sz - nr_sects;
	make_partition(&mbr.partition_record[PART_IDX_CACHE], start_sect, nr_sects);

	/* custom */
	start_sect += nr_sects;
	nr_sects	= (512 * 1024 *1024) / 512;
	userdata_sz = userdata_sz - nr_sects;
	make_partition(&mbr.partition_record[PART_IDX_CUSTOM], start_sect, nr_sects);

	/* userdata */
	start_sect += nr_sects;
	nr_sects	= userdata_sz;
	make_partition(&mbr.partition_record[PART_IDX_USERDATA], start_sect, nr_sects);

	/* the MBR already up to date */
	if (!memcmp(&old_mbr, &mbr, sizeof(mbr))) {
		LOGI("partition table is already the newest.\n");
		close(fd);
		return 1;
	}

	/* update MBR */
	lseek(fd, 0, SEEK_SET);
	if (write(fd, &mbr, sizeof(mbr)) < 0) {
		LOGE("write %s failed: %s", fname, strerror(errno));
		close(fd);
		return -1;
	}

	ensure_path_unmounted("/cache");
	ensure_path_unmounted("/data");
	sync();

	if (ioctl(fd, BLKRRPART, NULL) < 0) {
		LOGE("rescan partition error: %s\n", strerror(errno));
		close(fd);
		return -1;
	}

	close(fd);
	return 0;
}

static int handle_repartition(void)
{
	int ret;

	LOGI("Make partition table...\n");
	ret = make_partition_table();
	if (ret < 0) {
		LOGE("Make partition table failed.\n");
		return -1;
	} else if (ret > 0) {
		return 0;
	}

	if (ret == 0) {
        int result;

		LOGI("Make partition table success.\n");

		/* cache */
		LOGI("format cache...\n");
		result = make_ext4fs("/dev/block/mmcblk0p2", 0, NULL, NULL);
		/* userdata */
		LOGI("format userdata...\n");
		result |= make_ext4fs("/dev/block/mmcblk0p3", 0, NULL, NULL);
		/* custom */
		LOGI("format custom...\n");
		result |= make_ext4fs("/dev/block/mmcblk0p4", 0, NULL, NULL);

		if (result != 0) {
			LOGE("format failed!\n");
			return -1;
		}

		LOGI("format success.\n");
		sync();
	}

	return 0;
}

static void handle_low_power()
{
	enum ScreenRecoveryUI::Action action;
	int capacity = get_battery_capacity();

	/* not enough power to upgrade */
	ui->DrawError(ScreenRecoveryUI::ERR_LOW_POWER);
	ui->DrawBattery(capacity);

	while (capacity < 20) {
		int new_capacity = get_battery_capacity();
		if (capacity != new_capacity) {
			capacity = new_capacity;
			ui->DrawBattery(capacity);
		}
		ui->WaitAction(&action, 1000);
		if (action == ScreenRecoveryUI::ACTION_REBOOT) {
			ui->ClearScreen();
			reboot_system();
		}
	}
}

static void update_and_wipe(bool is_update, enum WipeDataType wipe_type)
{
	enum LOCK_TYPE lock_type;
	int passwd_len = 0;

	/* check password */
	if (wipe_type != WIPE_NONE && is_wipe_data_need_validate()
			&& (lock_type = get_lock_type()) != LOCK_DISABLE
			&& (passwd_len = get_passwd_length()) > 0
			&& (wipe_type!=WIPE_EXTERNAL_SDCARD)) {
		int passwd_ok = 0;
		int pw_err_num = 0;
		int countdown_time = 0;

		LOGI("screen lock enabled, passwd length: %d\n", passwd_len);
		

		ui->SetUnlockPasswdNum(passwd_len);

		if (lock_type == LOCK_SIMPLE) {
			ui->DrawDigitKeyboard();
		} else {
			ui->DrawQwertyKeyboard();
		}

		while (1) {
			enum ScreenRecoveryUI::Action action;

			if (passwd_ok) {
				break;
			}

			ui->WaitAction(&action, 0);
			switch (action) {
			case ScreenRecoveryUI::ACTION_REBOOT:
				ui->ClearScreen();
				reboot_system();
				return;
			case ScreenRecoveryUI::ACTION_CHECK_PASSWD:
				if (check_passwd(ui->GetInputPasswd())) {
					passwd_ok = 1;
					break;
				}
				LOGE("password error!\n");
				ui->DrawPasswdError();
				pw_err_num++;

				if (pw_err_num == MAX_PWD_ERR_NUM) {
					pw_err_num = 0;
					for (countdown_time=PWD_ERR_TIMEOUT-1; countdown_time>=0; countdown_time--) {
						if (countdown_time > 0) {
							ui->DrawPasswdErrorCountDownInfo();
							ui->DrawPasswdErrorCountDown(countdown_time);
						}
						sleep(1);
					}
					ui->DrawPasswdInfo();
				}

				break;
			case ScreenRecoveryUI::ACTION_NONE:
				break;
			default:
				LOGE("unknown Action.(%d)\n", action);
				break;
			}
		}
	}

	set_update_bootloader_message(false, WIPE_NONE);
	ui->DrawProgress();
	if(is_update){
		if(get_battery_capacity()<20){//without enough power,stop it.
			handle_low_power();
			ui->DrawProgress();
		}
		int wipe_cache;
		int result;
		ui->DrawWipeProgress(ScreenRecoveryUI::UPDATE_TXT_CHECK);
		result = install_package(ZIP_PACKAGE_FILE, &wipe_cache, TEMPORARY_INSTALL_FILE, false);

		switch(result){
			case INSTALL_CORRUPT_1://not found
				LOGE("firmware not found!\n");
				ui->ResetProgress();
				ui->DrawError(ScreenRecoveryUI::ERR_NOT_FOUND);
				break;
			case INSTALL_CORRUPT_2://decrypt error
			case INSTALL_VERIFY_FAILURE:
				LOGE("firmware corrupt.\n");
				ui->ResetProgress();
				ui->DrawError(ScreenRecoveryUI::ERR_CORRUPT);
				break;
			case INSTALL_ROOT_INC_ERROR:
				ui->ResetProgress();
				ui->DrawError(ScreenRecoveryUI::ERR_UNABLE);
				break;
			case INSTALL_FIRMWARE_TOO_OLD:
				ui->ResetProgress();
				ui->DrawError(ScreenRecoveryUI::ERR_FIRMWARE_TOO_OLD);
				break;
			case INSTALL_ERROR:
				ui->ResetProgress();
				LOGE("unknown error.\n");
				ui->DrawError(ScreenRecoveryUI::ERR_CORRUPT);
				break;
		}
		finish_package();
#ifdef MEIZU_MX2
		if (result == INSTALL_SUCCESS) {
			ensure_path_mounted("/system");
			easy_cp_func("/fstab.mx2.bak1", "/system/fstab.mx2.1");
			easy_cp_func("/fstab.mx2.bak2", "/system/fstab.mx2.2");
			ensure_path_unmounted("/system");
		}
#endif
		if (result == INSTALL_SUCCESS) {
			if(wipe_cache || wipe_type != WIPE_NONE){
				ui->DrawWipeProgress(ScreenRecoveryUI::UPDATE_TXT_CLEAR);
				do_wipe(WIPE_USERDATA);
				mzUserdataFlash();
			} else {
				/* create /data/app/.need_init file to notify system install apk */
				ensure_path_mounted("/data");
				if (creat("/data/app/.need_init", 0644) >= 0) {
					chown("/data/app/.need_init", 1000, 1000);
				}
				ensure_path_unmounted("/data");
			}
		}

		/* remove update_locate file */
		ensure_path_mounted(UPDATE_LOCATE_FILE);
		unlink(UPDATE_LOCATE_FILE);

		if (result == INSTALL_SUCCESS || result == INSTALL_MODEM) {
			reboot_system();
		}
	}else if(wipe_type != WIPE_NONE){
		ui->DrawWipeProgress(ScreenRecoveryUI::UPDATE_TXT_CLEAR);
		do_wipe((enum WipeDataType)wipe_type);
		if (wipe_type != WIPE_SDCARD) {
			mzUserdataFlash();
		}
		reboot_system();
	}
}

static void handle_upgrade(int bootmode)
{
	bool is_update = false;
	int wipe_type = WIPE_NONE;
	struct bootloader_message boot;

	ui = new ScreenRecoveryUI();
	ui->Init();

	backlight_set_brightness(BACKLIGHT_BRIGHTNESS);

#ifdef MEIZU_MX2
	if (CUSTOM_STAGE_2 == bootmode) {
		ui->DrawStage2();
		goto wait;
	}
#endif

#if defined(MEIZU_MX2) || defined(MEIZU_MX3)
	if (CUSTOM_REPARTITION == bootmode) {
		if (get_battery_capacity() < 20) {
			handle_low_power();
		}
		ui->DrawRepartition();
		goto wait;
	}
#endif

	if (BOOT_MODE_NONE == bootmode || CUSTOM_ENTER_RECOVERY == bootmode ||
		BOOT_MODE_MANUAL == bootmode) {
		if (get_battery_capacity() < 20) {
			handle_low_power();
		}
		ui->DrawMenu();
		goto wait;
	}

	if (BOOT_MODE_UPGRADE == bootmode) {
		is_update = true;
	}
	if (CUSTOM_UPDATE_LOCATE == bootmode) {
		is_update = true;
	}
	if (CUSTOM_WIPE_SDCARD == bootmode) {
		wipe_type = WIPE_SDCARD;
	}
	if (CUSTOM_WIPE_USERDATA == bootmode) {
		wipe_type = WIPE_USERDATA;
	}
	if (CUSTOM_WIPE_ALL == bootmode) {
		wipe_type = WIPE_ALL;
	}
	if (CUSTOM_UPDATE_AND_WIPE == bootmode) {
		is_update = true;
		wipe_type = WIPE_USERDATA;
	}
	if (CUSTOM_WIPE_EXTERNAL_SDCARD == bootmode) {
		wipe_type = WIPE_EXTERNAL_SDCARD;
	}

	LOGI("is_update = %d, is_wipe = %d\n", is_update, wipe_type);

	if (is_update || wipe_type) {
		update_and_wipe(is_update, (enum WipeDataType)wipe_type);
	} else {
		ui->DrawMenu();
	}

wait:
	while (1) {
		enum ScreenRecoveryUI::Action action;

		ui->WaitAction(&action, 0);
		switch (action) {
		case ScreenRecoveryUI::ACTION_REBOOT:
			ui->ClearScreen();
			return;
		case ScreenRecoveryUI::ACTION_UPDATE:
			closeUMS();
			update_and_wipe(true, WIPE_NONE);
			break;
		case ScreenRecoveryUI::ACTION_WIPE:
			closeUMS();
			update_and_wipe(false, WIPE_USERDATA);
			break;
		case ScreenRecoveryUI::ACTION_UPDATE_WIPE:
			closeUMS();
			update_and_wipe(true, WIPE_USERDATA);
			break;
		case ScreenRecoveryUI::ACTION_WIPE_ALL:
			closeUMS();
			update_and_wipe(false, WIPE_ALL);
			break;
#ifdef MEIZU_MX2
		case ScreenRecoveryUI::ACTION_FORMAT:
			umountSDCard();
			ui->DrawFormating();
			wipe_all();
			mzUserdataFlash();
			return;
#endif
		case ScreenRecoveryUI::ACTION_REPARTITION:
		{
			int ret;

			ui->DrawProgress();
			ui->DrawWipeProgress(ScreenRecoveryUI::UPDATE_TXT_CLEAR);

			/* backup update package into /ram0/ */
			ret = backup_update_package();

#ifdef MEIZU_MX2
			do_repartition();
#else
			handle_repartition();
#endif
			/*
			 * restore update package and reboot to upgrade.
			 */
			if (!ret) {
				restore_update_package();

				const char *command = "--update_package_wipe";
				FILE* fp = fopen_path(COMMAND_FILE, "w");
				fwrite(command, 1, strlen(command), fp);
				fflush(fp);
				fsync(fileno(fp));
				check_and_fclose(fp, COMMAND_FILE);

				android_reboot(ANDROID_RB_RESTART2, 0, "recovery");
				sleep(5);
			}
			return;
		}
		case ScreenRecoveryUI::ACTION_NONE:
			break;
		default:
			LOGE("unknown Action.(%d)\n", action);
			break;
		}
	}
	
	return;
}

static void long_power_handler(int key, void *data)
{
	ChargeUI *charge_ui = (ChargeUI *)data;
	int soc;
	
	if (key != KEY_POWER) {
		return;
	}
	
	soc = get_battery_capacity();

	if ((soc >= 6 && power_usb()) || (soc >= 0 && power_ac()) ) {
		LOGI("Long power key pressed.\n");
		LOGI("Rebooting...\n");
		android_reboot(ANDROID_RB_RESTART, 0, 0);
	} else {
		uart_printf("Low battery, please wait...\n");
		//charge_ui->DrawWaitNotice(true);
		usleep(1500 * 1000);
		//charge_ui->DrawWaitNotice(false);
	}
}

/**
 * Power off the device if charger(AC or USB) remove when charging.
 */
static void *charge_poweroff_listener(void *arg)
{
	while (1) {
		if (!is_charging()) {
			LOGI("Charger remove, poweroff.\n");
			android_reboot(ANDROID_RB_POWEROFF, 0, 0);
		}
		usleep(100 * 1000);
	}
	
	return NULL;
}

static void *charge_key_listener(void *arg)
{
	ChargeUI *charge_ui = (ChargeUI *)arg;
	key_val_t key;
	
	while (1) {
		if (charge_ui->WaitKey(&key) < 0) {
			continue;
		}

		if ((key.key_code==KEY_POWER) || (key.key_code==KEY_HOME)) {
			uart_printf("KEY_WAKEUP %s\n", key.updown ? "down" : "up");
			if (key.updown) {
				last_wakeup_key_time = time(NULL);
			} else {
				continue;
			}
		} else {
			continue;
		}

		pthread_mutex_lock(&gKeyMutex);
		pthread_cond_signal(&gKeyCond);
		pthread_mutex_unlock(&gKeyMutex);
	}
	
	return NULL;
}

static void handle_charge(Device *device, int bootmode)
{
	ChargeUI *charge_ui = new ChargeUI();
	
	charge_ui->Init();
	
	if (!is_charging()) {
		if (bootmode == BOOT_MODE_LOW_BAT) {
			charge_ui->DrawLowBattery();
			backlight_set_brightness(BACKLIGHT_BRIGHTNESS);
			sleep(2);
		}
		android_reboot(ANDROID_RB_POWEROFF, 0, 0);
	}

	pthread_t charge_poweroff_thread;
	pthread_t charge_key_thread;
	
	charge_ui->RegisterKeyLongPressHandler(long_power_handler, charge_ui);

	pthread_create(&charge_poweroff_thread, NULL, charge_poweroff_listener, NULL);
	pthread_create(&charge_key_thread, NULL, charge_key_listener, charge_ui);

	last_wakeup_key_time = time(NULL);

	//draw background bucket
	charge_ui->DrawBackground();
	backlight_set_brightness(BACKLIGHT_BRIGHTNESS);

	while (1) {
		int soc = get_battery_capacity();
		uart_printf("current battery capacity is %d\n", soc);

		if (soc == 100) {
			//draw still
			charge_ui->DrawCapacity(100,'g');
		} else {
			int i;
			char color = 'g';

			if ((power_usb() && soc < 6) || (power_ac() && soc < 3)) {
				color = 'r';
				soc = soc < 3 ? 3 : soc;
			}

			/* draw from current capacity - 10 */
			i = soc - 10;
			if (i < 3) i = 3;

			//draw from down to up
			for (; i <= soc; i++) {
				usleep(50 * 1000);
				charge_ui->DrawCapacity(i, color);
			}
		}
		usleep(800 * 1000);

		if (time(NULL) - last_wakeup_key_time >= 10) {
			backlight_set_brightness(0);
#ifndef MEIZU_MX2
			gr_fb_blank(true);
#endif
			if (soc > 2) {
				suspend_system(1);
			}
			pthread_mutex_lock(&gKeyMutex);
			pthread_cond_wait(&gKeyCond, &gKeyMutex);
			pthread_mutex_unlock(&gKeyMutex);
			suspend_system(0);
#ifndef MEIZU_MX2
			gr_fb_blank(false);
#endif
			backlight_set_brightness(BACKLIGHT_BRIGHTNESS);
		}
	}
}

#ifdef MEIZU_MX2
void check_sdcard_partition_r(void)
{
	int infd, outfd;
	int size;
	char buf[512];
	int i;

	infd = open("/dev/block/mmcblk0", O_RDONLY);
	if (infd < 0) {
		LOGE("open mmcblk0 error\n");
		goto err;
	}

	size = read(infd, buf, 512);
	if (size != 512) {
		LOGE("read size error (%d)\n", size);
		close(infd);
		goto err;
	}
	close(infd);

	if (buf[510] != 0x55 || buf[511] != 0xaa) {
		LOGE("mbr signature error\n");
		goto err;
	}

	/* if mbr changed */
	if (buf[492] == 0x10) {
		LOGI("good, new partition\n");
		return;
	}
	else if (buf[492] != 0x10) { /* if mbr not changed */
		LOGI("errr, old partition\n");
		bootmode = CUSTOM_REPARTITION;
		return;
	}
	else {
		LOGI("unknown partition\n");
		goto err;
	}

err:
	return;
}

void do_repartition(void)
{
	int infd, outfd;
	int size;
	int total_size;
	int data_start, data_size;
	char buf[512];
	int ret;

retry:
	infd = open("/sys/block/mmcblk0/size", O_RDONLY);
	if (infd < 0) {
		LOGE("open mmcblk0 error\n");
		goto err;
	}

	read(infd, buf, 512);
	total_size = strtol(buf, NULL, 10);
	close(infd);

	infd = open("/dev/block/mmcblk0", O_RDONLY);
	if (infd < 0) {
		LOGE("open mmcblk0 error\n");
		goto err;
	}

	size = read(infd, buf, 512);
	if (size != 512) {
		LOGE("read size error (%d)\n", size);
		close(infd);
		goto err;
	}
	close(infd);

	outfd = open("/dev/block/mmcblk0", O_RDWR);
	if (outfd < 0)
		goto err;

	buf[450] = 0x83;
	buf[455] = 0x40;
	buf[456] = 0x48;
	buf[475] = 0x00;
	buf[476] = 0x30;
	buf[487] = 0x00;
	buf[488] = 0x32;
	buf[492] = 0x10;
	buf[503] = 0x00;
	buf[504] = 0x42;

	// 454-457  :start sector of userdata
	// 458-461  :number of sectors of userdata
	data_start = *(int *)(buf + 454);
	data_size = total_size - data_start - 0x20000;
	buf[458] = *(char *)&data_size;
	buf[459] = *((char *)&data_size + 1);
	buf[460] = *((char *)&data_size + 2);
	buf[461] = *((char *)&data_size + 3);

	size = write(outfd, buf, 512);
	if (size != 512) {
		LOGE("write size error (%d)\n", size);
		usleep(200000);
		close(outfd);
		goto retry;
	}
	ensure_path_mounted("/system");
	easy_cp_func("/fstab.mx2.bak1", "/system/fstab.mx2.1");
	easy_cp_func("/fstab.mx2.bak2", "/system/fstab.mx2.2");
	usleep(100000);
	ensure_path_unmounted("/system");
	usleep(100000);

	ensure_path_unmounted("/cache");
	ensure_path_unmounted("/data");
	sync();

	if (ioctl(outfd, BLKRRPART, NULL) < 0) {
		LOGE("rescan partition error: %s\n", strerror(errno));
		close(outfd);
		goto err;
	}

	close(outfd);

	ret = make_ext4fs("/dev/block/mmcblk0p1", 0, NULL, NULL);
	LOGI("make_ext4fs data (%d)\n", ret);
	ret = make_ext4fs("/dev/block/mmcblk0p3", 0, NULL, NULL);
	LOGI("make_ext4fs custom (%d)\n", ret);
	ret = make_ext4fs("/dev/block/mmcblk0p4", 0, NULL, NULL);
	LOGI("make_ext4fs cache (%d)\n", ret);

	sync();
	//finish_recovery();
	//android_reboot(ANDROID_RB_RESTART, 0, 0);

err:
	return;
}
#endif

int
main(int argc, char **argv) {
    time_t start = time(NULL);

    // If these fail, there's not really anywhere to complain...
    freopen(TEMPORARY_LOG_FILE, "a", stdout); setbuf(stdout, NULL);
    freopen(TEMPORARY_LOG_FILE, "a", stderr); setbuf(stderr, NULL);

#if 0
    // If this binary is started with the single argument "--adbd",
    // instead of being the normal recovery binary, it turns into kind
    // of a stripped-down version of adbd that only supports the
    // 'sideload' command.  Note this must be a real argument, not
    // anything in the command file or bootloader control block; the
    // only way recovery should be run with this argument is when it
    // starts a copy of itself from the apply_from_adb() function.
    if (argc == 2 && strcmp(argv[1], "--adbd") == 0) {
        adb_main();
        return 0;
    }
#endif

    printf("Starting recovery on %s", ctime(&start));

	LOGI("Recovery version: %s\n", recovery_version());
	LOGI("Kernel version: %s\n", kernel_version());
	LOGI("Bootloader version: %s\n", bootloader_version_str());

    charge_init();
    
    if (backlight_init())
        LOGE("Can't get backlight sys class path!\n");
    
	/* get boot mode */
	if (boot_mode(&bootmode) < 0) {
		LOGE("Can't get boot mode\n");
		LOGI("Rebooting...\n");
		android_reboot(ANDROID_RB_RESTART, 0, 0);
		return EXIT_SUCCESS;
	}

	LOGI("boot mode = 0x%x\n", bootmode);

	/* charging */
	if (bootmode == BOOT_MODE_LOW_BAT ||
		bootmode == BOOT_MODE_CHARGE) {
		handle_charge(NULL, bootmode);
		/* Never return here */
	}

    load_volume_table();

#ifdef MEIZU_MX2
    check_sdcard_partition_r();
#endif

    ensure_path_mounted(LAST_LOG_FILE);
    rotate_last_logs(10);
	get_args(&argc, &argv);

    int previous_runs = 0;
    const char *send_intent = NULL;
    const char *update_package = NULL;
    int wipe_data = 0, wipe_cache = 0, show_text = 0;
    bool just_exit = false;

    int arg;
    while ((arg = getopt_long(argc, argv, "", OPTIONS, NULL)) != -1) {
#ifdef MEIZU_MX2
	if (bootmode == CUSTOM_REPARTITION)
		break;
#endif
        switch (arg) {
        case 'p': previous_runs = atoi(optarg); break;
        case 's': send_intent = optarg; break;
        case 'u':
			update_package = optarg;
			bootmode = CUSTOM_UPDATE_LOCATE;
			break;
        case 'U':
			bootmode = CUSTOM_UPDATE_AND_WIPE;
			break;
        case 'w':
			bootmode = CUSTOM_WIPE_USERDATA;
			wipe_data = wipe_cache = 1;
			break;
        case 'c': wipe_cache = 1; break;
        case 'd': bootmode = CUSTOM_WIPE_SDCARD; break;
        case 'a': bootmode = CUSTOM_WIPE_ALL; break;
        case 'P': bootmode = CUSTOM_REPARTITION; break;
        case 't': show_text = 1; break;
        case 'x': just_exit = true; break;
        case 'l': locale = optarg; break;
        case 'D': bootmode = CUSTOM_WIPE_EXTERNAL_SDCARD; break;
        case 'g': {
            if (stage == NULL || *stage == '\0') {
                char buffer[20] = "1/";
                strncat(buffer, optarg, sizeof(buffer)-3);
                stage = strdup(buffer);
            }
            break;
        }
        case '?':
            LOGE("Invalid command argument\n");
            continue;
        }
    }

    if (locale == NULL) {
        load_locale_from_cache();
    }
    printf("locale is [%s]\n", locale);
    printf("stage is [%s]\n", stage);
#if 0
	Device* device = make_device();
	ui = device->GetUI();

	ui->SetLocale(locale);
#endif
    struct selinux_opt seopts[] = {
      { SELABEL_OPT_PATH, "/file_contexts" }
    };

    sehandle = selabel_open(SELABEL_CTX_FILE, seopts, 1);

    if (!sehandle) {
        LOGW("Warning: No file_contexts\n");
    }

    //device->StartRecovery();

    property_list(print_property, NULL);
    printf("\n");

	LOGI("boot mode = 0x%x\n", bootmode);

	switch (bootmode) {
		case CUSTOM_WIPE_EXTERNAL_SDCARD:
			handle_upgrade(bootmode);
			break;
		case BOOT_MODE_NONE:
		case BOOT_MODE_UPGRADE:
		case BOOT_MODE_MANUAL:
		case BOOT_MODE_CUSTOM:
		case CUSTOM_UPDATE_LOCATE:
		case CUSTOM_ENTER_RECOVERY:
			if (is_system_locked()) {
				LOGE("system is locked\n");
				break;
			}
		case BOOT_MODE_WIPE:
		case BOOT_MODE_RECOVERY_RETRY:
		case CUSTOM_UPDATE_AND_WIPE:
		case CUSTOM_WIPE_SDCARD:
		case CUSTOM_WIPE_USERDATA:
		case CUSTOM_WIPE_ALL:
		case CUSTOM_STAGE_2:
#if defined(MEIZU_MX2) || defined(MEIZU_MX3)
		case CUSTOM_REPARTITION:
#endif
			handle_upgrade(bootmode);
			break;
		default:
			LOGE("unknown boot mode!(0x%x)\n", bootmode);
			break;
	}

	// Otherwise, get ready to boot the main system...
	finish_recovery();
	LOGI("Rebooting...\n");
	android_reboot(ANDROID_RB_RESTART, 0, 0);
	return EXIT_SUCCESS;
}
