import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327A

def state06 : KState := ⟨⟨360553343220285287, 360553349723473783⟩, ⟨916034105147345073, 916178159954119287⟩, true⟩

def words05 : List Nat := [360581319063530841, 360581318738859694, 360581318414130344, 360581318277556448, 360581318277922266, 360581318254690160, 360581318231411030, 360581317651519350, 360581316942959371, 360581316089772749]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360522923053742970, 360522929561042611⟩, ⟨1912752896769307881, 1912897086278318617⟩, true⟩

def words06 : List Nat := [360581315236478233, 360581315216025147, 360581314266129736, 360581312714953337, 360581311163800439, 360581309376882668, 360581308164939525, 360581306680069872, 360581305195249381, 360581302984487174]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604066041571067, 360604072552999438⟩, ⟨(-746781530835779099), (-746637206007902293)⟩, true⟩

def words07 : List Nat := [360581301203588463, 360581300351350768, 360581299499038898, 360581298915520790, 360581298364802222, 360581296976644454, 360581295588486730, 360581294872380265, 360581295334544862, 360581296029830289]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617355144846878, 360617361660441086⟩, ⟨(-1182769416080822743), (-1182624954675842299)⟩, true⟩

def words08 : List Nat := [360581296030226764, 360581295965767754, 360581295747081548, 360581296101914027, 360581296102280242, 360581296074108824, 360581295930014561, 360581295319365138, 360581295025155307, 360581296125548102]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568804786472434, 360568811306186371⟩, ⟨409435117590800990, 409579714102549292⟩, true⟩

def words09 : List Nat := [360581297308187698, 360581298490836439, 360581299024771352, 360581299170319384, 360581299170691933, 360581298672811371, 360581298603721611, 360581298872464936, 360581298872856946, 360581298492591937]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk327B
