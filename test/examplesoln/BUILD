load("@fildesh//tool/bazel:fildesh.bzl", "fildesh_test")

fildesh_test(
    name = "Verif4_Sync_OrientRing_test",
    srcs = ["Verif4_Sync_OrientRing_test.fildesh"],
    aliases = {"protocon": "//src:protocon"},
    args = ["--input_file=$(location //examplesoln:OrientRing.prot)"],
    data = [
        "//examplesoln:OrientRing.prot",
    ],
)

fildesh_test(
    name = "Verif4_OrientRingOdd_failure_test",
    srcs = ["Verif4_OrientRingOdd_failure_test.fildesh"],
    aliases = {"protocon": "//src:protocon"},
    args = ["--input_file=$(location //examplesoln:OrientRingOdd.prot)"],
    data = [
        "//examplesoln:OrientRingOdd.prot",
    ],
)

## PLA file output.
fildesh_test(
    name = "PLA_MatchRingThreeState_test",
    srcs = ["PLA_MatchRingThreeState_test.fildesh"],
    aliases = {"protocon": "//src:protocon"},
    args = [
        "--expect_file=$(location :MatchRingThreeState.pla)",
        "--input_file=$(location //examplesoln:MatchRingThreeState.prot)",
    ],
    data = [
        ":MatchRingThreeState.pla",
        "//examplesoln:MatchRingThreeState.prot",
    ],
)

## Promela file output.
fildesh_test(
    name = "Promela_OrientDaisy_test",
    srcs = ["Promela_OrientDaisy_test.fildesh"],
    aliases = {"protocon": "//src:protocon"},
    args = [
        "--expect_file=$(location :OrientDaisy.pml)",
        "--input_file=$(location //examplesoln:OrientDaisy.prot)",
    ],
    data = [
        ":OrientDaisy.pml",
        "//examplesoln:OrientDaisy.prot",
    ],
)

## UDP file output.
fildesh_test(
    name = "UDP_TokenRingRand_test",
    srcs = ["UDP_TokenRingRand_test.fildesh"],
    aliases = {"protocon": "//src:protocon"},
    args = [
        "--expect_file=$(location :TokenRingRand.h)",
        "--input_file=$(location //examplesoln:TokenRingRand.prot)",
    ],
    data = [
        ":TokenRingRand.h",
        "//examplesoln:TokenRingRand.prot",
    ],
)
