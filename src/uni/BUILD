
package(
    default_visibility = [
        "//test/uni:__pkg__",
    ],
)

cc_binary(
    name = "aperiodic",
    srcs = [
        "aperiodic.cc",
        "uniact.hh",
        "unifile.cc",
        "unifile.hh",
        "//src:namespace.hh",
    ],
    deps = [
        "//src/cx:cx_lib",
        "//src/fildesh:fildesh_cc_lib",
    ],
    copts = [
        "-Isrc",
    ],
)

cc_binary(
    name = "classify",
    srcs = [
        "classify.cc",
        "adjlist.hh",
        "livelock.cc",
        "livelock.hh",
        "uniact.hh",
        "unifile.cc",
        "unifile.hh",
        "//src:namespace.hh",
    ],
    deps = [
        "//src:pfmla_lib",
        "//src/cx:cx_lib",
        "//src/fildesh:fildesh_cc_lib",
    ],
    copts = [
        "-Isrc",
    ],
)

cc_binary(
    name = "generate",
    srcs = [
        "generate.cc",
        "adjlist.hh",
        "canonical.cc",
        "canonical.hh",
        "livelock.cc",
        "livelock.hh",
        "uniact.hh",
        "unifile.cc",
        "unifile.hh",
        "//src:namespace.hh",
    ],
    deps = [
        "//src:pfmla_lib",
        "//src/cx:cx_lib",
        "//src/fildesh:fildesh_cc_lib",
    ],
    copts = [
        "-Isrc",
    ],
)

cc_binary(
    name = "synthesize",
    srcs = [
        "synthesize.cc",
        "adjlist.hh",
        "uniact.hh",
        "unifile.cc",
        "unifile.hh",
        "//src:namespace.hh",
    ],
    deps = [
        "//src:prot_file_lib",
        "//src/cx:cx_lib",
    ],
    copts = [
        "-Isrc",
    ],
)

cc_binary(
    name = "xlate",
    srcs = [
        "xlate.cc",
        "adjlist.hh",
        "livelock.cc",
        "livelock.hh",
        "uniact.hh",
        "unifile.cc",
        "unifile.hh",
        "//src:namespace.hh",
    ],
    deps = [
        "//src:prot_file_lib",
        "//src/cx:cx_lib",
    ],
    copts = [
        "-Isrc",
    ],
)
