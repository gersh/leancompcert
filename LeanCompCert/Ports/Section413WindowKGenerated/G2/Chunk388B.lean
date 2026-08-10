import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388A

def state06 : KState := ⟨⟨360542477453367960, 360542486733228483⟩, ⟨1549756354304605853, 1550000100679678155⟩, true⟩

def words05 : List Nat := [360582371173684682, 360582372788872032, 360582374061771307, 360582374676163707, 360582374970729039, 360582375265417232, 360582375265851462, 360582375229544500, 360582374534755403, 360582373508850709]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604902816056041, 360604912100873818⟩, ⟨(-876429447879354122), (-876185508840991150)⟩, true⟩

def words06 : List Nat := [360582372482879404, 360582372230790566, 360582372442587292, 360582372654479879, 360582372654964121, 360582372299937419, 360582371286604725, 360582370933891226, 360582370667117615, 360582371247568244]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619520224002246, 360619529513834186⟩, ⟨(-1444699856368095775), (-1444455722404784103)⟩, true⟩

def words07 : List Nat := [360582371315044423, 360582371382562310, 360582372110185816, 360582373356262608, 360582374408316710, 360582375460401895, 360582376181510217, 360582376918281573, 360582377874278416, 360582378830405139]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586629032545922, 360586638327321490⟩, ⟨(-165774301526557518), (-165529975329526012)⟩, true⟩

def words08 : List Nat := [360582380227120192, 360582380966216329, 360582381281069011, 360582381595960797, 360582381596411252, 360582381265439538, 360582381642010478, 360582382020420782, 360582382020893765, 360582382073295378]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592605701202254, 360592615000949105⟩, ⟨(-398237998805843686), (-397993479251045914)⟩, true⟩

def words09 : List Nat := [360582382842668146, 360582383612165242, 360582384313514512, 360582384357724609, 360582384358209284, 360582383836685035, 360582383315079640, 360582383542112897, 360582383805564916, 360582384069115707]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk388B
