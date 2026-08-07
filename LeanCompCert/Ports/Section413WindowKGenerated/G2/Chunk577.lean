import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567460187516974, 360567481317395994⟩, ⟨831819028859042097, 832642727707371149⟩, true⟩

def state01 : KState := ⟨⟨360598198177652704, 360598219315142627⟩, ⟨(-941977727926178829), (-941153589891587365)⟩, true⟩

def words00 : List Nat := [360581911617839883, 360581911360400976, 360581911366788196, 360581911436191874, 360581911436934200, 360581911252159868, 360581911144759908, 360581910992367277, 360581910986637533, 360581911270057781]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584834220912990, 360584855366065539⟩, ⟨(-170659579510824387), (-169834999228111941)⟩, true⟩

def words01 : List Nat := [360581911402012468, 360581911534050538, 360581911966101235, 360581912548519580, 360581912832403598, 360581913116395954, 360581913167547048, 360581913168352403, 360581912970838337, 360581913022737667]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360614841230259813, 360614862383006954⟩, ⟨(-1902792228519161045), (-1901967209839094765)⟩, true⟩

def words02 : List Nat := [360581913325987293, 360581913764277219, 360581914025253084, 360581914286307782, 360581914469944328, 360581914803674177, 360581915437184086, 360581916070832104, 360581916475194067, 360581917046708621]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360627656894207222, 360627678054553412⟩, ⟨(-2642689724294250530), (-2641864266882414202)⟩, true⟩

def words03 : List Nat := [360581917918032275, 360581918789564468, 360581919748938307, 360581920408995619, 360581920811861570, 360581921214783457, 360581921917474090, 360581922770379512, 360581923563472241, 360581924356715093]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595035134084403, 360595056302117244⟩, ⟨(-759111111190432685), (-758285209915808801)⟩, true⟩

def words04 : List Nat := [360581924967082150, 360581925278157751, 360581925526705482, 360581925775477805, 360581925947514494, 360581926034228385, 360581926034946180, 360581925970440439, 360581925905784718, 360581926049655542]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550582839705078, 360550604015316569⟩, ⟨1808372747342992220, 1809199086323209270⟩, true⟩

def words05 : List Nat := [360581926577497200, 360581927105474937, 360581927433801467, 360581927559604093, 360581927608833829, 360581927658275424, 360581927658938625, 360581927606918416, 360581927255643466, 360581926714179506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576344139839543, 360576365323054118⟩, ⟨320214379179143619, 321041157351442873⟩, true⟩

def words06 : List Nat := [360581926172554578, 360581925574757579, 360581925129354367, 360581924885829394, 360581924642236105, 360581924145129957, 360581923547408964, 360581923158493686, 360581922769354917, 360581922552712271]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583519031255872, 360583540222166342⟩, ⟨(-94340895700706761), (-93513672899655007)⟩, true⟩

def words07 : List Nat := [360581922457255784, 360581922125778288, 360581921794148606, 360581921879515908, 360581921920387495, 360581921961389620, 360581921962107781, 360581921852034928, 360581921777608354, 360581921806547027]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578183598857167, 360578204797354172⟩, ⟨213933270198613978, 214760931388336236⟩, true⟩

def words08 : List Nat := [360581922134726700, 360581922238151383, 360581922238876470, 360581922059160935, 360581921879334510, 360581921439462811, 360581921157381000, 360581921166551977, 360581921167277081, 360581921027348779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618269747981653, 360618290954107632⟩, ⟨(-2102768416838216290), (-2101940314733217506)⟩, true⟩

def words09 : List Nat := [360581921198816043, 360581921434832052, 360581921969999674, 360581922588552983, 360581922953834214, 360581923319165713, 360581923842736221, 360581924574039240, 360581925203879742, 360581925833872114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk577
