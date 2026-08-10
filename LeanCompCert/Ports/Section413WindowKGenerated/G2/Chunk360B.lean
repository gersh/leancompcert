import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360A

def state06 : KState := ⟨⟨360557239142714806, 360557247084759209⟩, ⟨891358243353551888, 891551850015033742⟩, true⟩

def words05 : List Nat := [360581978770271483, 360581977604775094, 360581976439250980, 360581975729611188, 360581975411940146, 360581974899357794, 360581974386759639, 360581973152601190, 360581971892160886, 360581971207055799]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597698848019586, 360597706794627005⟩, ⟨(-567742505550583042), (-567548734323363324)⟩, true⟩

def words06 : List Nat := [360581970603904907, 360581970846850833, 360581970847286665, 360581970704957462, 360581970562547935, 360581970274213083, 360581971090616022, 360581971907066528, 360581972146653072, 360581972583368006]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360649491648306622, 360649499599499017⟩, ⟨(-2436308193342590222), (-2436114256713069566)⟩, true⟩

def words07 : List Nat := [360581972998524941, 360581973413799399, 360581974596092559, 360581975529598239, 360581975742961337, 360581975956348172, 360581976646272477, 360581977930686214, 360581979802521558, 360581981674366314]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360612074019612626, 360612081975421926⟩, ⟨(-1086327356218442137), (-1086133252988045103)⟩, true⟩

def words08 : List Nat := [360581983065992241, 360581983692186477, 360581985084976011, 360581986477830725, 360581987343202866, 360581987443281128, 360581987443713835, 360581987052537444, 360581986844551270, 360581987678977161]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360529438137241241, 360529446097623857⟩, ⟨1896430079790261520, 1896624348094799380⟩, true⟩

def words09 : List Nat := [360581988250907187, 360581988822903015, 360581988928761204, 360581988929246411, 360581988270008565, 360581987416423390, 360581986562743418, 360581986475426029, 360581985623092998, 360581984168208201]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360B
