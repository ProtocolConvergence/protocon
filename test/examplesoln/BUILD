load("@lace//tool:spawn.bzl", "lace_test")

lace_test(
    name = "Verif4_Sync_OrientRing_test",
    srcs = ["Verif4_Sync_OrientRing_test.lace"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = ["$(location //examplesoln:OrientRing.prot)"],
    data = [
        "//examplesoln:OrientRing.prot",
        "//src:protocon",
    ],
)

lace_test(
    name = "Verif4_OrientRingOdd_failure_test",
    srcs = ["Verif4_OrientRingOdd_failure_test.lace"],
    aliases = ["protocon=$(location //src:protocon)"],
    args = ["$(location //examplesoln:OrientRingOdd.prot)"],
    data = [
        "//examplesoln:OrientRingOdd.prot",
        "//src:protocon",
    ],
    expect_failure = True,
)

## PLA file output.
lace_test(
    name = "PLA_MatchRingThreeState_test",
    srcs = ["PLA_MatchRingThreeState_test.lace"],
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
lace_test(
    name = "Promela_OrientDaisy_test",
    srcs = ["Promela_OrientDaisy_test.lace"],
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
lace_test(
    name = "UDP_TokenRingRand_test",
    srcs = ["UDP_TokenRingRand_test.lace"],
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
