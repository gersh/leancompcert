import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620A

def state06 : KState := ⟨⟨362505975423214192, 362506032044527675⟩, ⟨(-1283379522371560398), (-1281006023079815606)⟩, true⟩

def words05 : List Nat := [371285389821205069, 371285389788714560, 371285389980137218, 371285390006225287, 371285390007898180, 371285389983128319, 371285390190346621, 371285390296233806, 371285390630271416, 371285390965217323]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497827335160900, 362497883975501560⟩, ⟨(-777640753488973223), (-775266073274736239)⟩, true⟩

def words06 : List Nat := [371285391286183603, 371285391527323961, 371285391989383809, 371285392452571616, 371285392992853229, 371285393187703821, 371285393350360147, 371285393513699430, 371285393783422459, 371285393987048422]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485074607446701, 362485131266768257⟩, ⟨14064896202710007, 16440754657533269⟩, true⟩

def words07 : List Nat := [371285394449499930, 371285394912812007, 371285395324608574, 371285395436493904, 371285395595537564, 371285395755628798, 371285396099838644, 371285396101944890, 371285396100381000, 371285396098512097]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497043261426515, 362497099939628147⟩, ⟨(-728978813990167457), (-726601783364266045)⟩, true⟩

def words08 : List Nat := [371285396351124557, 371285396479147637, 371285396709239188, 371285396940157496, 371285397131125765, 371285397133233357, 371285397130222635, 371285397239771806, 371285397541156378, 371285397731846597]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498232582959833, 362498289280336501⟩, ⟨(-802812133129406344), (-800433911829788866)⟩, true⟩

def words09 : List Nat := [371285397923018835, 371285398114868362, 371285398520902184, 371285398812633793, 371285399118830822, 371285399425842481, 371285399683652926, 371285399685760317, 371285399842744528, 371285400052919394]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620B
