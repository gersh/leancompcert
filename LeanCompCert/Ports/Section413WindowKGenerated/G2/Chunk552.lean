import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592789855781398, 360592809125548261⟩, ⟨(-609369020888848701), (-608650343630089229)⟩, true⟩

def state01 : KState := ⟨⟨360609652881168921, 360609672158171463⟩, ⟨(-1540236893532830097), (-1539517816827750827)⟩, true⟩

def words00 : List Nat := [360581783578681928, 360581784114808566, 360581784487140760, 360581784859543693, 360581785100127768, 360581785505672613, 360581786238277042, 360581786971002161, 360581787393441973, 360581787899295012]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360648429484169983, 360648448768422820⟩, ⟨(-3681400320732998918), (-3680680843703226920)⟩, true⟩

def words01 : List Nat := [360581788379159660, 360581788859229124, 360581789666307164, 360581790334624346, 360581790723581542, 360581791112593377, 360581791828643982, 360581792709417902, 360581793917138877, 360581795124995443]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619636723925093, 360619656015499433⟩, ⟨(-2091550815592826708), (-2090830934234158222)⟩, true⟩

def words02 : List Nat := [360581796144867434, 360581796838037697, 360581797431343574, 360581798024853395, 360581798495416834, 360581798748915409, 360581798795886223, 360581798842938901, 360581799216957808, 360581799903275607]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556679957285425, 360556699256088756⟩, ⟨1385920469602659711, 1386640750255930835⟩, true⟩

def words03 : List Nat := [360581800639473424, 360581801375787566, 360581801862202612, 360581802022080093, 360581802099243482, 360581802176607664, 360581802177242668, 360581802113461818, 360581801823230152, 360581801369598096]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360619478668799275, 360619497974859810⟩, ⟨(-2083434757851370253), (-2082714076276511691)⟩, true⟩

def words04 : List Nat := [360581800915808771, 360581800650958363, 360581800941661884, 360581801250938684, 360581801270384719, 360581801271154349, 360581801248865753, 360581801356962467, 360581801791681449, 360581802474755260]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360617681126962443, 360617700440353921⟩, ⟨(-1984206398507935195), (-1983485311861523823)⟩, true⟩

def words05 : List Nat := [360581802905020299, 360581803335336931, 360581803815769032, 360581804460575460, 360581804960249486, 360581805460030599, 360581805775654600, 360581806099249450, 360581806749424717, 360581807399839607]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599266808868026, 360599286129494883⟩, ⟨(-966560692393003808), (-965839205883005030)⟩, true⟩

def words06 : List Nat := [360581808291201060, 360581808856474931, 360581809221014922, 360581809585627511, 360581809724761415, 360581810066735373, 360581810517256770, 360581810967907762, 360581811201869336, 360581811518833180]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611476409389000, 360611495737285806⟩, ⟨(-1641446320313251605), (-1640724431958788225)⟩, true⟩

def words07 : List Nat := [360581811980918863, 360581812443227167, 360581813103577884, 360581813592888344, 360581813749558864, 360581813906281608, 360581814317468631, 360581814945105595, 360581815482655627, 360581816020349449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618720371401882, 360618739706619778⟩, ⟨(-2042075073406517382), (-2041352780305800414)⟩, true⟩

def words08 : List Nat := [360581816394712523, 360581816526747705, 360581816876249148, 360581817225965634, 360581817493036162, 360581817937222047, 360581818216815506, 360581818496476448, 360581818874120221, 360581819542753945]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582056240125709, 360582075582593680⟩, ⟨(-14640884588100966), (-13918190593531384)⟩, true⟩

def words09 : List Nat := [360581820537412884, 360581821532184279, 360581822272641450, 360581822687338883, 360581823019550244, 360581823351962020, 360581823722943046, 360581823891363550, 360581823896600156, 360581823901962344]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552
