load("@fildesh//tool:spawn.bzl", "fildesh_test")

fildesh_test(
    name = "Verif4_Sync_OrientRing_test",
    srcs = ["Verif4_Sync_OrientRing_test.fildesh"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = ["$(location //examplesoln:OrientRing.prot)"],
    data = [
        "//examplesoln:OrientRing.prot",
        "//src:protocon",
    ],
)

fildesh_test(
    name = "Verif4_OrientRingOdd_failure_test",
    srcs = ["Verif4_OrientRingOdd_failure_test.fildesh"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = ["$(location //examplesoln:OrientRingOdd.prot)"],
    data = [
        "//examplesoln:OrientRingOdd.prot",
        "//src:protocon",
    ],
    expect_failure = True,
)

## PLA file output.
fildesh_test(
    name = "PLA_MatchRingThreeState_test",
    srcs = ["PLA_MatchRingThreeState_test.fildesh"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = [
        "$(location :MatchRingThreeState.pla)",
        "$(location //examplesoln:MatchRingThreeState.prot)",
    ],
    data = [
        ":MatchRingThreeState.pla",
        "//examplesoln:MatchRingThreeState.prot",
        "//src:protocon",
    ],
)

## Promela file output.
fildesh_test(
    name = "Promela_OrientDaisy_test",
    srcs = ["Promela_OrientDaisy_test.fildesh"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = [
        "$(location :OrientDaisy.pml)",
        "$(location //examplesoln:OrientDaisy.prot)",
    ],
    data = [
        ":OrientDaisy.pml",
        "//examplesoln:OrientDaisy.prot",
        "//src:protocon",
    ],
)

## UDP file output.
fildesh_test(
    name = "UDP_TokenRingRand_test",
    srcs = ["UDP_TokenRingRand_test.fildesh"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = [
        "$(location :TokenRingRand.h)",
        "$(location //examplesoln:TokenRingRand.prot)",
    ],
    data = [
        ":TokenRingRand.h",
        "//examplesoln:TokenRingRand.prot",
        "//src:protocon",
    ],
)
