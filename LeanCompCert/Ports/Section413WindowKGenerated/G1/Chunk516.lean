import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk516

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497755809191346, 362497794379806442⟩, ⟨(-661399721390857406), (-660055157846126536)⟩, true⟩

def state01 : KState := ⟨⟨362489841942131614, 362489880528119970⟩, ⟨(-253033961992056538), (-251688605106840190)⟩, true⟩

def words00 : List Nat := [371285003303031563, 371285003304758079, 371285003246632255, 371285003166645595, 371285003120040659, 371285003121961683, 371285003264892197, 371285003525108048, 371285003785283551, 371285003881569684]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362512011521950448, 362512050123555628⟩, ⟨(-1397351141826314541), (-1396004978880096923)⟩, true⟩

def words01 : List Nat := [371285004084800511, 371285004288899929, 371285004866927897, 371285004991426075, 371285005044797443, 371285005098713415, 371285005476842624, 371285005718611711, 371285006243697788, 371285006769515992]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476508090443932, 362476546707620633⟩, ⟨435449940845701809, 436796907674180967⟩, true⟩

def words02 : List Nat := [371285007295289712, 371285007380297827, 371285007535181489, 371285007690973369, 371285007833215742, 371285007834943497, 371285007527304939, 371285007220883496, 371285006913791027, 371285006845286219]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470689142238607, 362470727775006090⟩, ⟨736024062889189114, 737371834750111368⟩, true⟩

def words03 : List Nat := [371285006893288520, 371285007105897462, 371285007316482575, 371285007318222094, 371285007192926402, 371285007115896607, 371285007333390118, 371285007335118194, 371285007132347235, 371285006857785915]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496446043793330, 362496484692039938⟩, ⟨(-594108786525360451), (-592760215244858783)⟩, true⟩

def words04 : List Nat := [371285006656152564, 371285006658078485, 371285006833893169, 371285007077991574, 371285007214934998, 371285007216699918, 371285007447140047, 371285007751015665, 371285008209798887, 371285008433782695]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495309948490735, 362495348612494401⟩, ⟨(-535434386419242645), (-534085001208457505)⟩, true⟩

def words05 : List Nat := [371285008657728236, 371285008882219776, 371285009216056820, 371285009363283281, 371285009625659830, 371285009888715055, 371285010118310118, 371285010120041212, 371285010147265321, 371285010349564755]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474836637298022, 362474875316685061⟩, ⟨522383614870518269, 523733794867873435⟩, true⟩

def words06 : List Nat := [371285010828048438, 371285010949004267, 371285011020282138, 371285011092158843, 371285011279189726, 371285011306876648, 371285011352760758, 371285011399301007, 371285011444078120, 371285011445867718]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523419008195672, 362523457703242801⟩, ⟨(-1988113837586327076), (-1986762848356138166)⟩, true⟩

def words07 : List Nat := [371285011386345064, 371285011523893684, 371285012034519242, 371285012235108088, 371285012395001629, 371285012555402474, 371285013030703712, 371285013402634671, 371285014147699425, 371285014893537956]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497396665132454, 362497435375789604⟩, ⟨(-643184703793070610), (-641832907757190380)⟩, true⟩

def words08 : List Nat := [371285015552092130, 371285015712402116, 371285016246002356, 371285016780458782, 371285017429794462, 371285017645498900, 371285017859667977, 371285018074456990, 371285018409070452, 371285018651258116]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477362628116522, 362477401354325562⟩, ⟨392581517763559814, 393934117755776306⟩, true⟩

def words09 : List Nat := [371285019266392879, 371285019882190882, 371285020497895924, 371285020615601885, 371285020745861596, 371285020876991264, 371285021244339916, 371285021246069747, 371285021115198179, 371285020969756042]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk516
