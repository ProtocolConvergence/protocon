
cc_library(
    name = "cx_lib",
    srcs = [
        "alphatab.c",
        "alphatab.h",
        "bittable.h",
        "bittable.hh",
        "def.h",
        "lgtable.h",
        "lgtable.hh",
        "map.hh",
        "sesp.c",
        "sesp.h",
        "set.hh",
        "synhax.h",
        "synhax.hh",
        "syscx.c",
        "syscx.h",
        "table.h",
        "table.hh",
        "tuple.hh",
        "urandom.c",
        "urandom.h",
        "urandom.hh",
    ],
    deps = [
        "@fildesh//:fildesh_lib",
    ],
    visibility = ["//src:__subpackages__"],
)

cc_test(
    name = "testcxx",
    srcs = ["testcxx.cc"],
    deps = [":cx_lib"],
)

cc_test(
    name = "bittable_test",
    srcs = ["bittable_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

cc_test(
    name = "lgtable_test",
    srcs = ["lgtable_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

cc_test(
    name = "table_test",
    srcs = ["table_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

