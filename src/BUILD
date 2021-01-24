load("@rules_foreign_cc//tools/build_defs:cmake.bzl", "cmake_external")

exports_files([
    "namespace.hh",
])

cmake_external(
    name = "mdd_glu_lib",
    lib_source = "@mdd_glu//:all",
    static_libraries = [
        "libcmu.a",
        "libglu.a",
        "libcal.a",
        "libcu.a",
    ],
)

cc_library(
    name = "pfmla_glu_lib",
    srcs = [
        "pfmla-glu.c",
        "pfmla-glu.h",
        "pfmla.h",
    ],
    deps = [
        ":mdd_glu_lib",
        "//src/cx:cx_lib",
    ],
    copts = [
        "-Isrc",
        "-Iexternal/lace/src",
        "-Iexternal/mdd_glu/include",
    ],
)

cc_library(
    name = "pfmla_lib",
    srcs = [
        "pfmla.c",
        "pfmla.cc",
        "pfmla.h",
        "pfmla.hh",
    ],
    deps = [
        ":pfmla_glu_lib",
    ],
    copts = [
        "-Isrc",
        "-Iexternal/lace/src",
    ],
    visibility = [
        "//src/uni:__pkg__",
    ],
)

cc_library(
    name = "xnsys_lib",
    srcs = [
        "namespace.hh",
        "xfmlae.cc",
        "xfmlae.hh",
        "xnsys.cc",
        "xnsys.hh",
        "xnpc.cc",
        "xnpc.hh",
        "xnspec.cc",
        "xnspec.hh",
    ],
    deps = [
        ":pfmla_lib",
    ],
    copts = [
        "-Isrc",
        "-Iexternal/lace/src",
    ],
    visibility = [
        "//src/uni:__pkg__",
    ],
)
