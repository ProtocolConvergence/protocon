
genrule(
    name = "act_embed_h",
    srcs = [
        "protocol.c",
        "protocol.h",
    ],
    tools = ["@fildesh//tool:cembed"],
    cmd = "$(location @fildesh//tool:cembed) -o \"$@\" $(location protocol.h) $(location protocol.c)",
    outs = ["act.embed.h"],
    visibility = [
        "//src:__pkg__",
    ],
)

cc_binary(
    name = "udp_ThreeColorRing",
    srcs = [
        "protocol.c",
        "protocol.h",
        "act.h",
    ],
    linkopts = [
        "-lrt",
    ],
    # Uncomment when Bazel version 4 is on Gentoo.
    # target_compatible_with = [
    #     "@platforms//os:linux",
    # ],
)
