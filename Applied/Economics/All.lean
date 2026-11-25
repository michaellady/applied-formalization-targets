import Applied.Economics.Arrow
import Applied.Economics.AssetPricing
import Applied.Economics.BlackScholes
import Applied.Economics.BondarevaShapley
import Applied.Economics.EFX
import Applied.Economics.EFXAllButOne
import Applied.Economics.EFXBinary
import Applied.Economics.EFXFewGoods
import Applied.Economics.EFXOrdered
import Applied.Economics.EFXThree
import Applied.Economics.EFXTwoExtraGoods
import Applied.Economics.EFXTwoTypes
import Applied.Economics.FairDivisionBasic
import Applied.Economics.Finance
import Applied.Economics.GibbardSatterthwaite
import Applied.Economics.Kelly
import Applied.Economics.MatrixValue
import Applied.Economics.MatroidSecretary
import Applied.Economics.MatroidSecretaryBlocks
import Applied.Economics.MatroidSecretaryDirectSum
import Applied.Economics.MatroidSecretaryGraphic
import Applied.Economics.MatroidSecretaryLaminar
import Applied.Economics.MatroidSecretaryModel
import Applied.Economics.MatroidSecretaryUniform
import Applied.Economics.MatroidSecretaryUniformTop
import Applied.Economics.Minimax
import Applied.Economics.MonopolyPricing
import Applied.Economics.MonopolyPricingMeasure
import Applied.Economics.MulticommodityFlow
import Applied.Economics.Nash
import Applied.Economics.NashExistence
import Applied.Economics.NashTwoPlayer
import Applied.Economics.PMMS
import Applied.Economics.SecondWelfare
import Applied.Economics.SecretaryArrivalOptimal
import Applied.Economics.SecretaryOneOverE
import Applied.Economics.SecretaryRankOptimal
import Applied.Economics.Shapley
import Applied.Economics.ShapleyStochastic
import Applied.Economics.StableMatching
import Applied.Economics.StableMatchingMenOptimal
import Applied.Economics.StableMatchingOpposition
import Applied.Economics.StochasticGame
import Applied.Economics.VCG
import Applied.Economics.Vickrey
import Applied.Economics.Welfare
import Applied.Economics.EFXBridge
import Applied.Economics.EFXSanity
import Applied.Economics.PMMSSanity
import Applied.Economics.MatroidSecretarySanity
import Applied.Economics.SecretarySanity

/-!
# All of `Applied/Economics`

This module imports every file of `Applied/Economics/` and declares nothing. Its only purpose
is to be built: the library `Applied` is compiled file by file, so two files that are never
imported together can declare the same name without any build failing (this happened with
`sum_filter_eq_and_ne_add` in `EFXOrdered.lean` and `PMMS.lean`). Building this module turns
such a clash into an error. When a file is added to `Applied/Economics/`, add it here.
-/
