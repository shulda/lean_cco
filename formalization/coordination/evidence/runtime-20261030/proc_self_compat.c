#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
/* The sandbox getpid namespace is not the mounted proc namespace. Only map
   references to THIS process's executable to the correct proc/self alias. */
static const char *self_exe(const char *path) {
  char expected[64];
  snprintf(expected,sizeof(expected),"/proc/%ld/exe",(long)getpid());
  if(path && strcmp(path,expected)==0) return "/proc/self/exe";
  return path;
}
ssize_t readlink(const char *path,char *buf,size_t size) {
  static ssize_t (*next)(const char*,char*,size_t);
  if(!next) next=dlsym(RTLD_NEXT,"readlink");
  return next(self_exe(path),buf,size);
}
ssize_t readlinkat(int dirfd,const char *path,char *buf,size_t size) {
  static ssize_t (*next)(int,const char*,char*,size_t);
  if(!next) next=dlsym(RTLD_NEXT,"readlinkat");
  return next(dirfd,self_exe(path),buf,size);
}
char *realpath(const char *path,char *resolved) {
  static char *(*next)(const char*,char*);
  if(!next) next=dlsym(RTLD_NEXT,"realpath");
  return next(self_exe(path),resolved);
}
