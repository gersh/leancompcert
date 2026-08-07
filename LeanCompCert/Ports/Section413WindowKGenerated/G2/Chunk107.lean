import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk107

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360757226887680182, 360757227514717784⟩, ⟨(-1860441909921870534), (-1860437362647488770)⟩, true⟩

def state01 : KState := ⟨⟨360606832425846628, 360606833054124593⟩, ⟨(-251812163353525428), (-251807602801362528)⟩, true⟩

def words00 : List Nat := [360583381119192232, 360583382504685897, 360583382504793655, 360583379041564084, 360583375578947481, 360583369875518304, 360583359604100274, 360583344042346954, 360583328483475249, 360583323801692387]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360527678085686065, 360527678715189050⟩, ⟨596904170922305680, 596908744600654090⟩, true⟩

def words01 : List Nat := [360583334673911287, 360583345544125776, 360583352019063148, 360583357365645957, 360583360479358242, 360583363592523937, 360583366377713224, 360583366377843598, 360583365695612371, 360583360501065977]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360764652760424044, 360764653391156284⟩, ⟨(-1944766036760663076), (-1944761449898638514)⟩, true⟩

def words02 : List Nat := [360583355430233589, 360583359883632419, 360583372990247900, 360583386094446187, 360583390775223568, 360583390935359964, 360583393792165593, 360583396648477469, 360583408148719562, 360583425038728865]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360880627070478232, 360880627702452627⟩, ⟨(-3190236004174556179), (-3190231403978031281)⟩, true⟩

def words03 : List Nat := [360583435135526360, 360583445230454654, 360583463963154825, 360583487003102262, 360583505800274032, 360583524593966261, 360583538981025119, 360583558011913050, 360583585672138792, 360583613327256833]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360813527535688490, 360813528168890499⟩, ⟨(-2469382550570394181), (-2469377937183051209)⟩, true⟩

def words04 : List Nat := [360583644832619010, 360583672204619264, 360583695203753851, 360583718198622161, 360583735059413312, 360583756184099257, 360583778443872283, 360583800699527734, 360583818593203415, 360583839959683630]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360898889797720646, 360898890432156663⟩, ⟨(-3387372827295462727), (-3387368200636234551)⟩, true⟩

def words05 : List Nat := [360583863654976218, 360583887345901380, 360583919638687454, 360583948452772362, 360583969780657382, 360583991104586240, 360584017067033746, 360584050000587872, 360584079260958710, 360584108515918746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360791272550524824, 360791273186205490⟩, ⟨(-2229580616301156904), (-2229575976243363332)⟩, true⟩

def words06 : List Nat := [360584131616480244, 360584146201748706, 360584165926820504, 360584185648267648, 360584203147373547, 360584220992150667, 360584232583646689, 360584244173004210, 360584255918067552, 360584275138090797]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360642586072744751, 360642586709659530⟩, ⟨(-627135786009687213), (-627131132654349379)⟩, true⟩

def words07 : List Nat := [360584302932846597, 360584330722467221, 360584351617906454, 360584364015013440, 360584373948703427, 360584383880584145, 360584396150708354, 360584405882550846, 360584411279775697, 360584416676021246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360768161319050827, 360768161957200313⟩, ⟨(-1981321253781255024), (-1981316587109580936)⟩, true⟩

def words08 : List Nat := [360584430632591307, 360584449123486135, 360584472129389156, 360584495131050783, 360584510789955527, 360584517970205145, 360584521361788845, 360584524752780116, 360584536694125380, 360584553710781114]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360703511672367186, 360703512311765918⟩, ⟨(-1283499281246166047), (-1283494601089024275)⟩, true⟩

def words09 : List Nat := [360584564276506100, 360584574840286018, 360584590246749812, 360584612421528679, 360584629118056327, 360584645811512250, 360584656746021762, 360584659213898944, 360584670218921667, 360584681221951177]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk107
