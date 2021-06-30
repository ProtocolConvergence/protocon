
cc_library(
    name = "cx_lib",
    srcs = [
        "alphatab.c",
        "alphatab.h",
        "alphatab.hh",
        "associa.h",
        "associa.hh",
        "bittable.h",
        "bittable.hh",
        "bstree.c",
        "bstree.h",
        "def.h",
        "fileb.c",
        "fileb.h",
        "fileb.hh",
        "lgtable.h",
        "lgtable.hh",
        "map.hh",
        "ofile.c",
        "ofile.h",
        "ofile.hh",
        "ospc.c",
        "ospc.h",
        "rbtree.c",
        "rbtree.h",
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
        "xfile.c",
        "xfile.h",
        "xfile.hh",
    ],
    deps = [
        "@lace//:lace_lib",
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
    name = "fileb_test",
    srcs = ["fileb_test.c"],
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
    name = "ospc_test",
    srcs = ["ospc_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

cc_test(
    name = "rbtree_test",
    srcs = ["rbtree_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

cc_test(
    name = "table_test",
    srcs = ["table_test.c"],
    deps = [":cx_lib"],
    size = "small",
)

cc_test(
    name = "tmpdir_test",
    srcs = ["tmpdir_test.c"],
    deps = [":cx_lib"],
    size = "small",
)
