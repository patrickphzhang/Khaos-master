#include <stdio.h>
#define PRINT_LOG //printf("%s detected, exit(1)\n", __FUNCTION__);

#ifdef _WIN32
#include <Shlwapi.h>

#include <TlHelp32.h>

#include <Windows.h>

#include <tchar.h>

#pragma comment(lib, "Advapi32.lib")

#pragma comment(lib, "Shlwapi.lib")

#pragma comment(lib, "Mpr.lib")

#define EXPORT extern "C" __declspec(dllexport)


BOOL Is_RegKeyExists(HKEY hKey, const TCHAR *lpSubKey) {

  HKEY hkResult = NULL;

  if (RegOpenKeyEx(hKey, lpSubKey, NULL, KEY_READ, &hkResult) ==
      ERROR_SUCCESS) {

    RegCloseKey(hkResult);

    return TRUE;
  }

  return FALSE;
}

BOOL Is_RegKeyValueExists(HKEY hKey, const TCHAR *lpSubKey,
                          const TCHAR *lpValueName, const TCHAR *search_str) {

  HKEY hkResult = NULL;

  TCHAR lpData[1024] = {0};

  DWORD cbData = MAX_PATH;

  if (RegOpenKeyEx(hKey, lpSubKey, NULL, KEY_READ, &hkResult) ==
      ERROR_SUCCESS) {

    if (RegQueryValueEx(hkResult, lpValueName, NULL, NULL, (LPBYTE)lpData,
                        &cbData) == ERROR_SUCCESS) {

      if (StrStrI((PCTSTR)lpData, search_str) != NULL) {

        RegCloseKey(hkResult);

        return TRUE;
      }
    }

    RegCloseKey(hkResult);
  }

  return FALSE;
}

DWORD GetProcessIdFromName(LPCTSTR szProcessName) {

  PROCESSENTRY32 pe32;

  HANDLE hSnapshot = NULL;

  SecureZeroMemory(&pe32, sizeof(PROCESSENTRY32));

  // We want a snapshot of processes

  hSnapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);

  // Check for a valid handle, in this case we need to check for

  // INVALID_HANDLE_VALUE instead of NULL

  if (hSnapshot == INVALID_HANDLE_VALUE) {

    //printf("CreateToolhelp32Snapshot\n");

    return 0;
  }

  // Now we can enumerate the running process, also

  // we can't forget to set the PROCESSENTRY32.dwSize member

  // otherwise the following functions will fail

  pe32.dwSize = sizeof(PROCESSENTRY32);

  if (Process32First(hSnapshot, &pe32) == FALSE) {

    // Cleanup the mess

    //printf("Process32First\n");

    CloseHandle(hSnapshot);

    return 0;
  }

  // Do our first comparison

  if (StrCmpI(pe32.szExeFile, szProcessName) == 0) {

    // Cleanup the mess

    CloseHandle(hSnapshot);

    return pe32.th32ProcessID;
  }

  // Most likely it won't match on the first try so

  // we loop through the rest of the entries until

  // we find the matching entry or not one at all

  while (Process32Next(hSnapshot, &pe32)) {

    if (StrCmpI(pe32.szExeFile, szProcessName) == 0) {

      // Cleanup the mess

      CloseHandle(hSnapshot);

      return pe32.th32ProcessID;
    }
  }

  // If we made it this far there wasn't a match, so we'll return 0

  // _tprintf(_T("\n-> Process %s is not running on this system ..."),

  // szProcessName);

  CloseHandle(hSnapshot);

  return 0;
}

BOOL find_str_in_data(PBYTE needle, size_t needleLen, PBYTE haystack,
                      size_t haystackLen) {

  for (size_t i = 0; i < haystackLen - needleLen; i++) {

    if (memcmp(&haystack[i], needle, needleLen) == 0) {

      return TRUE;
    }
  }

  return FALSE;
}

BOOL vbox_reg_keys() {

  /* Array of strings of blacklisted registry keys */

  const TCHAR *szKeys[] = {_T("HARDWARE\\ACPI\\DSDT\\VBOX__"),

                           _T("HARDWARE\\ACPI\\FADT\\VBOX__"),

                           _T("HARDWARE\\ACPI\\RSDT\\VBOX__"),

                           _T("SOFTWARE\\Oracle\\VirtualBox Guest Additions"),

                           _T("SYSTEM\\ControlSet001\\Services\\VBoxGuest"),

                           _T("SYSTEM\\ControlSet001\\Services\\VBoxMouse"),

                           _T("SYSTEM\\ControlSet001\\Services\\VBoxService"),

                           _T("SYSTEM\\ControlSet001\\Services\\VBoxSF"),

                           _T("SYSTEM\\ControlSet001\\Services\\VBoxVideo")};

  WORD dwlength = sizeof(szKeys) / sizeof(szKeys[0]);

  /* Check one by one */

  for (int i = 0; i < dwlength; i++) {

    TCHAR msg[256] = _T("");

    /*_stprintf_s(msg, sizeof(msg) / sizeof(TCHAR), _T("Checking reg key %s "),
                szKeys[i]);*/

    if (Is_RegKeyExists(HKEY_LOCAL_MACHINE, szKeys[i])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vbox_reg_key_value() {

  /* Array of strings of blacklisted registry key values */

  const TCHAR *szEntries[][3] = {

      {_T("HARDWARE\\DEVICEMAP\\Scsi\\Scsi Port 0\\Scsi Bus 0\\Target Id ")
       _T("0\\Logical Unit Id 0"),
       _T("Identifier"), _T("VBOX")},

      {_T("HARDWARE\\Description\\System"), _T("SystemBiosVersion"),
       _T("VBOX")},

      {_T("HARDWARE\\Description\\System"), _T("VideoBiosVersion"),
       _T("VIRTUALBOX")},

      {_T("HARDWARE\\Description\\System"), _T("SystemBiosDate"),
       _T("06/23/99")},

  };

  WORD dwLength = sizeof(szEntries) / sizeof(szEntries[0]);

  for (int i = 0; i < dwLength; i++) {

    TCHAR msg[256] = _T("");

  /*  _stprintf_s(
        msg, sizeof(msg) / sizeof(TCHAR),
        _T("Checking reg key HARDWARE\\Description\\System - %s is set to %s"),
        szEntries[i][1],

        szEntries[i][2]);*/

    if (Is_RegKeyValueExists(HKEY_LOCAL_MACHINE, szEntries[i][0],
                             szEntries[i][1], szEntries[i][2])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vbox_devices() {

  const TCHAR *devices[] = {_T("\\\\.\\VBoxMiniRdrDN"), _T("\\\\.\\VBoxGuest"),
                            _T("\\\\.\\pipe\\VBoxMiniRdDN"),
                            _T("\\\\.\\VBoxTrayIPC"),

                            _T("\\\\.\\pipe\\VBoxTrayIPC")};

  WORD iLength = sizeof(devices) / sizeof(devices[0]);

  for (int i = 0; i < iLength; i++) {

    HANDLE hFile = CreateFile(devices[i], GENERIC_READ, FILE_SHARE_READ, NULL,
                              OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);

    TCHAR msg[256] = _T("");

 /*   _stprintf_s(msg, sizeof(msg) / sizeof(TCHAR), _T("Checking device %s "),
                devices[i]);*/

    if (hFile != INVALID_HANDLE_VALUE) {

      CloseHandle(hFile);

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vbox_processes() {

  const TCHAR *szProcesses[] = {_T("vboxservice.exe"), _T("vboxtray.exe")};

  WORD iLength = sizeof(szProcesses) / sizeof(szProcesses[0]);

  for (int i = 0; i < iLength; i++) {

    TCHAR msg[256] = _T("");

  /*  _stprintf_s(msg, sizeof(msg) / sizeof(TCHAR),
                _T("Checking VirtualBox process %s "), szProcesses[i]);*/

    if (GetProcessIdFromName(szProcesses[i])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vbox_network_share() {

  TCHAR szProviderName[MAX_PATH] = _T("");

  DWORD lpBufferSize = MAX_PATH;

  if (WNetGetProviderName(WNNC_NET_RDR2SAMPLE, szProviderName, &lpBufferSize) ==
      NO_ERROR) {

    if (StrCmpI(szProviderName, _T("VirtualBox Shared Folders")) == 0) {

      PRINT_LOG

      return TRUE;
    }
  }

  return FALSE;
}

BOOL vmware_reg_keys() {

  /* Array of strings of blacklisted registry keys */

  const TCHAR *szKeys[] = {

      _T("SOFTWARE\\VMware, Inc.\\VMware Tools"),

  };

  WORD dwlength = sizeof(szKeys) / sizeof(szKeys[0]);

  /* Check one by one */

  for (int i = 0; i < dwlength; i++) {

    TCHAR msg[256] = _T("");

   /* _stprintf_s(msg, sizeof(msg) / sizeof(TCHAR), _T("Checking reg key %s "),
                szKeys[i]);*/

    if (Is_RegKeyExists(HKEY_LOCAL_MACHINE, szKeys[i])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vmware_reg_key_value() {

  /* Array of strings of blacklisted registry key values */

  const TCHAR *szEntries[][3] = {

      {_T("HARDWARE\\DEVICEMAP\\Scsi\\Scsi Port 0\\Scsi Bus 0\\Target Id ")

       _T("0\\Logical Unit Id 0"),

       _T("Identifier"), _T("VMWARE")},

      {_T("HARDWARE\\DEVICEMAP\\Scsi\\Scsi Port 1\\Scsi Bus 0\\Target Id ")
       _T("0\\Logical Unit Id 0"),
       _T("Identifier"), _T("VMWARE")},

      {_T("HARDWARE\\DEVICEMAP\\Scsi\\Scsi Port 2\\Scsi Bus 0\\Target Id ")
       _T("0\\Logical Unit Id 0"),
       _T("Identifier"), _T("VMWARE")},

      {_T("SYSTEM\\ControlSet001\\Control\\SystemInformation"),
       _T("SystemManufacturer"), _T("VMWARE")},

      {_T("SYSTEM\\ControlSet001\\Control\\SystemInformation"),
       _T("SystemProductName"), _T("VMWARE")},

  };

  WORD dwLength = sizeof(szEntries) / sizeof(szEntries[0]);

  for (int i = 0; i < dwLength; i++) {

    TCHAR msg[256] = _T("");

   /* _stprintf_s(msg, sizeof(msg) / sizeof(TCHAR), _T("Checking reg key %s"),
                szEntries[i][0]);*/

    if (Is_RegKeyValueExists(HKEY_LOCAL_MACHINE, szEntries[i][0],
                             szEntries[i][1], szEntries[i][2])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vmware_devices() {

  const TCHAR *devices[] = {

      _T("\\\\.\\HGFS"),

      _T("\\\\.\\vmci"),

  };

  WORD iLength = sizeof(devices) / sizeof(devices[0]);

  for (int i = 0; i < iLength; i++) {

    HANDLE hFile = CreateFile(devices[i], GENERIC_READ, FILE_SHARE_READ, NULL,
                              OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);

    TCHAR msg[256] = _T("");

   /* _stprintf_s(msg, sizeof(msg) / sizeof(TCHAR), _T("Checking device %s "),
                devices[i]);*/

    if (hFile != INVALID_HANDLE_VALUE) {

      CloseHandle(hFile);

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL vmware_processes() {

  const TCHAR *szProcesses[] = {

      _T("vmtoolsd.exe"),      _T("vmwaretray.exe"), _T("vmwareuser.exe"),
      _T("VGAuthService.exe"), _T("vmacthlp.exe"),

  };

  WORD iLength = sizeof(szProcesses) / sizeof(szProcesses[0]);

  for (int i = 0; i < iLength; i++) {

    TCHAR msg[256] = _T("");

    //_stprintf_s(msg, sizeof(msg) / sizeof(TCHAR),
    //            _T("Checking VWware process %s "), szProcesses[i]);

    if (GetProcessIdFromName(szProcesses[i])) {

      PRINT_LOG

      return true;
    }
  }

  return false;
}

BOOL(*testList[])

() = {&vbox_reg_keys,        &vbox_reg_key_value,
      &vbox_devices,         &vbox_processes,

      &vbox_network_share,   &vmware_reg_keys,
      &vmware_reg_key_value, &vmware_processes};

#endif

#ifdef __linux__
#include <stdlib.h>
#include <string.h>
#define EXPORT extern "C" __attribute__((visibility("default")))

// TODO: robustness improvement

bool fileIsEmpty(const char *name) // will remove the file
{
  FILE *f = fopen(name, "r");
  bool flag = !(fgetc(f) == EOF);
  fclose(f);
  char cmd[20];
  sprintf(cmd, "rm %s", name);
  system(cmd);
  return flag;
}

bool processExist(const char *processName) {
  char cmd[100];
  sprintf(cmd, "ps -A | grep '%s' >> plist", processName);
  system(cmd);
  return fileIsEmpty("plist");
}

bool deviceExist(const char *deviceName) {
  char cmd[100];
  sprintf(cmd, "ls -a /dev | grep '%s' >> dlist", deviceName);
  system(cmd);
  return fileIsEmpty("dlist");
}

bool smbiosMatch(const char *key, const char *value) {
  char cmd[100];
  sprintf(cmd, "cat /sys/devices/virtual/dmi/id/%s | grep '%s' >> smbiosInfo",
          key, value);
  system(cmd);
  return fileIsEmpty("smbiosInfo");
}

bool vmware_devices() {
  const char *deviceList[] = {"vmci"};
  for (auto d : deviceList) {
    if (deviceExist(d)) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool vmware_processes() {
  const char *processList[] = {"vmwgfx", "vmblock", "vmtoolsd", "vmhgfs"};
  for (auto p : processList) {
    if (processExist(p)) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool vmware_smbios() {
  const char *smbiosKeyValue[][2] = {
      {"product_name", "VMware Virtual Platform"},
      {"sys_vendor", "VMware, Inc."}};
  for (auto pair : smbiosKeyValue) {
    if (smbiosMatch(pair[0], pair[1])) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool vbox_processes() {
  const char *processList[] = {"vmwgfx", "VBoxClient", "VBoxService",
                               "VBoxWQueue"};
  for (auto p : processList) {
    if (processExist(p)) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool vbox_devices() {

  const char *deviceList[] = {"vboxguest", "vboxuser"};
  for (auto d : deviceList) {
    if (deviceExist(d)) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool vbox_smbios() {
  const char *smbiosKeyValue[][2] = {
      {"bios_vendor", "innotek GmbH"}, {"board_version", "VirtualBox"},
      {"board_name", "VirtualBox"},    {"product_family", "Virtual Machine"},
      {"product_name", "VirtualBox"},  {"sys_vendor", "innotek GmbH"}};
  for (auto pair : smbiosKeyValue) {
    if (smbiosMatch(pair[0], pair[1])) {
      PRINT_LOG
      return true;
    }
  }
  return false;
}

bool (*testList[])

    () = {&vmware_processes, &vmware_devices, &vmware_smbios,
          &vbox_devices,     &vbox_processes, &vbox_smbios};

#endif

EXPORT void antivm_helper() {
  for (auto test : testList) {
    if (test())
    {
//printf("found vm, exiting\n");
      exit(10086);
    }
  }
}