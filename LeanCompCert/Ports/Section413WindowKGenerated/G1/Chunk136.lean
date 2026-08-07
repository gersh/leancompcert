import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk136

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452515625057094, 362452518018280417⟩, ⟨436884993705686188, 436907014729450696⟩, true⟩

def state01 : KState := ⟨⟨362426190531575163, 362426192928457490⟩, ⟨795101949932698091, 795124020737462323⟩, true⟩

def words00 : List Nat := [371284641172355194, 371284639661628177, 371284635464987851, 371284635472549207, 371284635472865413, 371284634574577466, 371284626493314917, 371284621161743048, 371284615830727955, 371284614972596907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461628481577923, 362461630882176210⟩, ⟨312638488072308047, 312660609470364931⟩, true⟩

def words01 : List Nat := [371284610680637285, 371284606229654079, 371284602709733993, 371284602710183911, 371284600954617892, 371284599429972546, 371284597905411549, 371284595623684112, 371284588559145979, 371284586874060966]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459570671390216, 362459573075636139⟩, ⟨340886514749861819, 340908685847618623⟩, true⟩

def words02 : List Nat := [371284587930188630, 371284587930604695, 371284586342518682, 371284584488656196, 371284582634904730, 371284582375522686, 371284581902275522, 371284584352037275, 371284584717607520, 371284584718031416]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362565179979574116, 362565182387525415⟩, ⟨(-1098972140934690452), (-1098949919314096368)⟩, true⟩

def words03 : List Nat := [371284585407934588, 371284587932592686, 371284595823533552, 371284598320226182, 371284599722099509, 371284601123894804, 371284606052751923, 371284608303686571, 371284614211156171, 371284620117947372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362507382003576804, 362507384415227596⟩, ⟨(-310620344745007622), (-310598072644439962)⟩, true⟩

def words04 : List Nat := [371284626021236600, 371284626466439338, 371284629104411912, 371284631742204036, 371284636029849672, 371284636030259424, 371284633177744407, 371284630326704567, 371284629977193952, 371284631644540875]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362361484409484037, 362361486824814691⟩, ⟨1681815300940797064, 1681837623290921318⟩, true⟩

def words05 : List Nat := [371284634485960937, 371284637327124358, 371284639266473779, 371284639266883669, 371284634074161204, 371284630535834879, 371284626997817045, 371284625655708781, 371284617186997787, 371284608173518273]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362420976340477689, 362420978759482378⟩, ⟨869014769095674111, 869037141651440051⟩, true⟩

def words06 : List Nat := [371284599161181484, 371284594035669110, 371284587335735438, 371284584164897274, 371284580994382871, 371284576926646061, 371284565741295041, 371284559161277792, 371284552582015289, 371284551337511013]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362439778934206888, 362439781356963934⟩, ⟨611795947177610232, 611818371046333154⟩, true⟩

def words07 : List Nat := [371284546687648908, 371284541283316077, 371284535879606053, 371284533098844248, 371284528075405035, 371284524532653058, 371284520990282982, 371284516789288022, 371284508191085632, 371284504922098900]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362394841100779106, 362394843527191877⟩, ⟨1226869026574213703, 1226891500472465961⟩, true⟩

def words08 : List Nat := [371284503711743321, 371284503712154050, 371284498667682760, 371284493624764279, 371284488582433156, 371284482422753835, 371284473602497151, 371284470105523054, 371284466608922391, 371284463067036470]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492449468857378, 362492451898986432⟩, ⟨(-109626116874405746), (-109603592081486238)⟩, true⟩

def words09 : List Nat := [371284456521443333, 371284455296515520, 371284458165205521, 371284458165616825, 371284456311951086, 371284452996337482, 371284451682393179, 371284451682850021, 371284451636332518, 371284452220708826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk136
