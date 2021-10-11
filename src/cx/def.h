/**
 * \file def.h
 * All important definitions.
 **/
#ifndef DEF_H_
#define DEF_H_

#include "fildesh.h"

#ifndef __OPENCL_VERSION__
#include <float.h>
#endif  /* #ifndef __OPENCL_VERSION__ */

typedef int Bit;
/* enum Trit { Nil = -1, Yes = 1, May = 0 }; */
enum Trit { Nil = 0, Yes = 1, May = 2 };
typedef enum Trit Trit;


typedef int_fast8_t sign_t;
typedef sign_t Sign;

/** Type of function which compares two objects.
 * Return values should conform to:
 *  -1: lhs < rhs
 *   0: lhs == rhs
 *  +1: lhs > rhs
 **/
typedef sign_t (* PosetCmpFn) (const void*, const void*);

typedef bool Bool;
#define MPI_Bool MPI_CHAR

typedef unsigned char byte;
#define BYTE_BIT CHAR_BIT
#define BYTE_MAX UCHAR_MAX

#if !defined(__OPENCL_VERSION__)
typedef unsigned int uint;
#endif  /* #ifndef __OPENCL_VERSION__ */
#ifndef INT_BIT
#define INT_BIT (BYTE_BIT * sizeof(int))
#endif

typedef size_t zuint;
#ifndef SIZE_MAX
#define SIZE_MAX (~(size_t)0)
#endif
#ifndef SIZE_BIT
#define SIZE_BIT (BYTE_BIT * sizeof(size_t))
#endif

typedef byte bitint;
#define BITINT_MAX BYTE_MAX

typedef unsigned long int luint;
typedef unsigned long int ulong;
#ifndef LONG_BIT
#define LONG_BIT (BYTE_BIT * sizeof(long))
#endif

typedef zuint ujint;
typedef bitint ujintlg;

#if !defined(__OPENCL_VERSION__)
typedef struct uint2 uint2;
struct uint2 { uint s[2]; };
#endif  /* #ifndef __OPENCL_VERSION__ */
typedef struct ujint2 ujint2;
struct ujint2 { zuint s[2]; };

#ifndef uint32
/* #define uint32 uint */
#define uint32 uint32_t
#endif

#if 0
typedef double real;
#define Max_real DBL_MAX
#define Min_real (-DBL_MAX)
#define Small_real DBL_MIN
#define Epsilon_real DBL_EPSILON
#define realPackSz 2
#define GL_REAL GL_DOUBLE

#define REAL_MAX DBL_MAX
#define REAL_MIN (-DBL_MAX)
#define REAL_SMALL DBL_MIN
#define REAL_EPSILON DBL_EPSILON

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define MPI_real MPI_DOUBLE

#else
typedef float real;
#define Max_real FLT_MAX
#define Min_real (-FLT_MAX)
#define Small_real FLT_MIN
#define Epsilon_real FLT_EPSILON

#define REAL_MAX FLT_MAX
#define REAL_MIN (-FLT_MAX)
#define REAL_SMALL FLT_MIN
#define REAL_EPSILON FLT_EPSILON

#define realPackSz 4
#define GL_REAL GL_FLOAT

#ifndef M_PI
#define M_PI 3.14159265358979323846f
#endif

#define MPI_real MPI_FLOAT

#endif


#ifdef _MSC_VER
/* Disable warning: 'fopen' unsafe, use fopen_s instead */
/* REF CMakeLists.txt: Define _CRT_SECURE_NO_WARNINGS */

/* Disable: conditional expression is constant */
# pragma warning (disable : 4127)
/* Disable: conversion from 'uint' to 'real' */
# pragma warning (disable : 4244)
/* Disable: conversion from 'double' to 'float' */
# pragma warning (disable : 4305)
#endif


#if __STDC_VERSION__ < 199901L
#ifdef _MSC_VER
#define restrict
#else
#define restrict __restrict
#endif
#endif

#define qual_inline static inline

#ifdef _MSC_VER
# define __FUNC__ __FUNCTION__
#else
# define __FUNC__ __extension__ __func__
#endif


#ifndef __OPENCL_VERSION__
#include "synhax.h"
#endif

#endif
