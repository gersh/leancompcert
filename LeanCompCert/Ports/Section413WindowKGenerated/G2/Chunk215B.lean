import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215A

def state06 : KState := ⟨⟨360611989536941856, 360611992252967792⟩, ⟨(-690778921878858831), (-690739299597777501)⟩, true⟩

def words05 : List Nat := [360579969307735820, 360579967888892112, 360579966470102984, 360579964989835466, 360579962924626449, 360579959042492655, 360579955160665332, 360579953421519026, 360579954251764295, 360579955737982505]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588178301671849, 360588181020342856⟩, ⟨(-177711835835782890), (-177672156513538240)⟩, true⟩

def words06 : List Nat := [360579956146005409, 360579956146283510, 360579954822563797, 360579955231591345, 360579955231824731, 360579954509266229, 360579952657078181, 360579949063362554, 360579945469927153, 360579944399114655]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360526091730778076, 360526094452070292⟩, ⟨1161845726595867358, 1161885462470456542⟩, true⟩

def words07 : List Nat := [360579944399341565, 360579944183457722, 360579943967566759, 360579942177471178, 360579941334363243, 360579939913842179, 360579939211936259, 360579939212214643, 360579937793106774, 360579935298338618]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360649815171263895, 360649817895187669⟩, ⟨(-1508954997297905779), (-1508915204621450217)⟩, true⟩

def words08 : List Nat := [360579932803741493, 360579930249408457, 360579929963296506, 360579930619570384, 360579930619827024, 360579929425796873, 360579927020601488, 360579926752667281, 360579928353230336, 360579931590494906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578118283614582, 360578121010191627⟩, ⟨39256101917042769, 39295951890941091⟩, true⟩

def words09 : List Nat := [360579933754890802, 360579935919114400, 360579937270698193, 360579940061262239, 360579941358475194, 360579942655609437, 360579942655858028, 360579942570770260, 360579940351131570, 360579940267223616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk215B
