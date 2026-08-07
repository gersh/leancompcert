import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586529883779010, 360586556781186560⟩, ⟨(-232944210399931037), (-231766823396002123)⟩, true⟩

def state01 : KState := ⟨⟨360570785136903596, 360570812042900638⟩, ⟨787302199301830769, 788480142948734853⟩, true⟩

def words00 : List Nat := [360582980198715855, 360582980199628158, 360582979973268645, 360582979627768569, 360582979282131580, 360582978804681656, 360582978511622500, 360582978413545242, 360582978315380852, 360582978068868062]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597872246946236, 360597899161569261⟩, ⟨(-968403839936428078), (-967225337197395886)⟩, true⟩

def words01 : List Nat := [360582977931815044, 360582977982750334, 360582977983501174, 360582977984091401, 360582977878289452, 360582977556855006, 360582977235255768, 360582977218198813, 360582977449142700, 360582977680302428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562196912952750, 360562223836261804⟩, ⟨1344072758081363013, 1345251823891494469⟩, true⟩

def words02 : List Nat := [360582977719981857, 360582977720894573, 360582977523374714, 360582977292476164, 360582977061343200, 360582976768046176, 360582976237571237, 360582975524269024, 360582974810812164, 360582974288581587]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557955776848871, 360557982708752759⟩, ⟨1619089087470074141, 1620268710527692799⟩, true⟩

def words03 : List Nat := [360582973969253244, 360582973720298249, 360582973471251439, 360582973103266303, 360582972864074158, 360582972565488468, 360582972266635966, 360582972080412371, 360582971814834872, 360582971430383353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569073502319053, 360569100442853546⟩, ⟨898111684325312957, 899291867033298967⟩, true⟩

def words04 : List Nat := [360582971045749969, 360582970593747725, 360582970283741450, 360582970142131430, 360582970000462846, 360582969621256602, 360582969004892231, 360582968492165469, 360582967979169247, 360582967703717591]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360557113729334396, 360557140678562812⟩, ⟨1673789919541006849, 1674970666092549463⟩, true⟩

def words05 : List Nat := [360582967490698489, 360582967158826395, 360582966826789042, 360582966757691719, 360582966758471414, 360582966571851763, 360582966385135918, 360582966049585620, 360582965476947360, 360582965079828501]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568477529961861, 360568504487801192⟩, ⟨936702452677299164, 937883757776457928⟩, true⟩

def words06 : List Nat := [360582964682417438, 360582964424224711, 360582964244999052, 360582963946556653, 360582963647974557, 360582963290132580, 360582963081181648, 360582962909934341, 360582962738606927, 360582962384483426]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609689495880115, 360609716462338785⟩, ⟨(-1736985946203658227), (-1735804081925437523)⟩, true⟩

def words07 : List Nat := [360582962176632625, 360582962191933149, 360582962334488332, 360582962335401859, 360582962295459166, 360582962052198119, 360582961808753535, 360582961977972629, 360582962391079958, 360582962804381519]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552750675427984, 360552777650609970⟩, ⟨1957368476232840789, 1958550906521667187⟩, true⟩

def words08 : List Nat := [360582963088390183, 360582963135688557, 360582963136445308, 360582963014779906, 360582962892877888, 360582962660951127, 360582962192154092, 360582961583003999, 360582960973704792, 360582960281316114]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360523387948041737, 360523414931822832⟩, ⟨3862957072348192984, 3864140060676914438⟩, true⟩

def words09 : List Nat := [360582959816926798, 360582959589754186, 360582959362489057, 360582958979997744, 360582958432366906, 360582957825516966, 360582957218425959, 360582956554335844, 360582955756778392, 360582954840307839]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648
