load("@rules_foreign_cc//tools/build_defs:make.bzl", "make")
load("@rules_foreign_cc//tools/build_defs:cmake.bzl", "cmake_external")

exports_files([
    "namespace.hh",
])

cmake_external(
    name = "mdd_glu_lib",
    lib_source = "@mdd_glu//:all",
    static_libraries = [
        "libcu.a",
        "libglu.a",
        "libcal.a",
    ],
)


make(
    name = "peg",
    lib_source = "@peg//:all",
    binaries = [
        "peg",
        "leg",
    ],
)
filegroup(
    name = "peg_leg",
    srcs = [":peg"],
    output_group = "leg",
)

genrule(
    name = "prot_xfile_leg",
    srcs = ["prot-xfile.leg"],
    tools = [":peg_leg"],
    cmd = "$(location peg_leg) -o \"$@\" $(location prot-xfile.leg)",
    outs = ["prot-xfile.leg.cc"],
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
        "-Iexternal/lace/src",
    ],
    visibility = [
        "//src/uni:__pkg__",
    ],
)

cc_test(
    name = "pfmla_test",
    srcs = [
        "namespace.hh",
        "pfmla_test.cc",
    ],
    deps = [
        ":pfmla_lib",
    ],
    copts = [
        "-Iexternal/lace/src",
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
        "-Iexternal/lace/src",
    ],
)

cc_test(
    name = "xnsys_test",
    srcs = [
        "inst.cc",
        "inst.hh",
        "namespace.hh",
        "xnpc.hh",
        "xnsys.hh",
        "xfmlae.hh",
        "xnspec.hh",
        "xnsys_test.cc",
    ],
    deps = [
        ":xnsys_lib",
    ],
    copts = [
        "-Iexternal/lace/src",
    ],
)

cc_library(
    name = "prot_file_lib",
    srcs = [
        "namespace.hh",
        "pla.cc",
        "pla.hh",
        "prot-ofile.cc",
        "prot-ofile.hh",
        "prot-xfile.cc",
        "prot-xfile.hh",
        "prot-xfile.leg.cc",
    ],
    deps = [
        ":xnsys_lib",
    ],
    copts = [
        "-Isrc",
        "-Iexternal/lace/src",
    ],
    visibility = [
        "//src/uni:__pkg__",
    ],
)

cc_test(
    name = "conflictfamily_test",
    srcs = [
        "conflictfamily.cc",
        "conflictfamily.hh",
        "conflictfamily_test.cc",
        "namespace.hh",
    ],
    deps = ["//src/cx:cx_lib"],
    copts = [
        "-Iexternal/lace/src",
    ],
)

cc_test(
    name = "stabilization_test",
    srcs = [
        "inst.cc",
        "inst.hh",
        "stabilization.cc",
        "stabilization.hh",
        "stabilization_test.cc",
        "namespace.hh",
    ],
    deps = [":xnsys_lib"],
    copts = [
        "-Iexternal/lace/src",
    ],
)
