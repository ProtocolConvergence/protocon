
genrule(
    name = "act_embed_h",
    srcs = [
        "protocol.c",
        "protocol.h",
    ],
    tools = ["@lace//tool:cembed"],
    cmd = "$(location @lace//tool:cembed) -o \"$@\" $(location protocol.h) $(location protocol.c)",
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
)
