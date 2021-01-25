
cc_library(
    name = "cx_lib",
    srcs = [
        "alphatab.hh",
        "associa.hh",
        "bittable.hh",
        "fileb.hh",
        "kautz.cc",
        "kautz.hh",
        "lgtable.hh",
        "map.hh",
        "ofile.hh",
        "sesp.c",
        "sesp.h",
        "set.hh",
        "synhax.hh",
        "table.hh",
        "tuple.hh",
        "urandom.hh",
        "xfile.hh",
    ],
    deps = [
        "@lace//src/cx:cx_lib",
    ],
    copts = [
        "-Iexternal/lace/src",
    ],
    visibility = ["//visibility:public"],
)

cc_test(
    name = "testcxx",
    srcs = ["testcxx.cc"],
    deps = [":cx_lib"],
    copts = [
        "-Iexternal/lace/src",
    ],
)
