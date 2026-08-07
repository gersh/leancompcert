import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360498013449011378, 360498028105884715⟩, ⟨4077843104778074355, 4078322464001404067⟩, true⟩

def state01 : KState := ⟨⟨360545269101050521, 360545283764200330⟩, ⟨1790388892816084229, 1790868555852900017⟩, true⟩

def words00 : List Nat := [360582289226317945, 360582287719494828, 360582286427391116, 360582285442758708, 360582284458125502, 360582283075110480, 360582281265145501, 360582279880782243, 360582278496280882, 360582277537302022]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525225963218597, 360525240632728816⟩, ⟨2760821409975052145, 2761301380950104695⟩, true⟩

def words01 : List Nat := [360582276773745065, 360582275665785272, 360582274557727304, 360582273875171914, 360582273408191376, 360582272707334734, 360582272006432342, 360582271093531171, 360582269925853903, 360582268748816179]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549544625262463, 360549559301046072⟩, ⟨1583177570194360451, 1583657844958340737⟩, true⟩

def words02 : List Nat := [360582267571599314, 360582266644392406, 360582265811283448, 360582264766310782, 360582263721275753, 360582262419717982, 360582261443706811, 360582260780030239, 360582260116313671, 360582259235899641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557845963729096, 360557860645815304⟩, ⟨1180946290534512518, 1181426870563119854⟩, true⟩

def words03 : List Nat := [360582258561253572, 360582258072455214, 360582257583496403, 360582256711888143, 360582255557418830, 360582254036971714, 360582252516459642, 360582251420994635, 360582250638105795, 360582250135298441]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360545744650726640, 360545759339157695⟩, ⟨1767009814079351041, 1767490701483014161⟩, true⟩

def words04 : List Nat := [360582249632403803, 360582248866508841, 360582247819638933, 360582247109464460, 360582246399137827, 360582245582611429, 360582244339870777, 360582242770140028, 360582241200346321, 360582240055390575]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360507269847584325, 360507284542291668⟩, ⟨3631394766078802993, 3631875957601054091⟩, true⟩

def words05 : List Nat := [360582239302991818, 360582238677001479, 360582238050964517, 360582237181870949, 360582236328258677, 360582235193352716, 360582234058291464, 360582233211935742, 360582231939558317, 360582230393666020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360536784809932810, 360536799510947046⟩, ⟨2200891200099426922, 2201372697283944256⟩, true⟩

def words06 : List Nat := [360582228847696875, 360582227102797774, 360582225617171166, 360582224556062044, 360582223494947661, 360582222064661379, 360582220575418344, 360582219232373761, 360582217889177546, 360582216731852430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360524923282617888, 360524937989979589⟩, ⟨2775895568667749083, 2776377373545964907⟩, true⟩

def words07 : List Nat := [360582215795448867, 360582214615104021, 360582213434679907, 360582212678654337, 360582212136325404, 360582211300527558, 360582210464698093, 360582209285585783, 360582207680704672, 360582206500159993]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557097933504248, 360557112647160591⟩, ⟨1215925781917476462, 1216407891991378396⟩, true⟩

def words08 : List Nat := [360582205319442708, 360582204562944956, 360582203821778277, 360582202864651190, 360582201907451423, 360582200844336140, 360582199996316075, 360582199572394786, 360582199148421790, 360582198394572251]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590237632477830, 360590252352429016⟩, ⟨(-391185811237412294), (-390703395895414856)⟩, true⟩

def words09 : List Nat := [360582197877783931, 360582197785108660, 360582197904739923, 360582197905407437, 360582197693106113, 360582197102263935, 360582196511306730, 360582196444971067, 360582196611615587, 360582196778401771]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484
