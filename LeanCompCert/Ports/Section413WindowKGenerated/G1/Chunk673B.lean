import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk673A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk673B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk673A

def state06 : KState := ⟨⟨362470443804648238, 362470510940706993⟩, ⟨1007178297765475325, 1010232615682847375⟩, true⟩

def words05 : List Nat := [371285509308510525, 371285509308619209, 371285509307951260, 371285509265124819, 371285509083686287, 371285508954560163, 371285508894825212, 371285508897124276, 371285508675819994, 371285508455785421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472577713941780, 362472644870605075⟩, ⟨863437662611611999, 866493368556077009⟩, true⟩

def words06 : List Nat := [371285508234728259, 371285508106734000, 371285507880504125, 371285507771857835, 371285507662521340, 371285507519102712, 371285507164459747, 371285506896885908, 371285506628059825, 371285506580098264]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464815405060490, 362464882582637678⟩, ⟨1386459851256213856, 1389516966277452486⟩, true⟩

def words07 : List Nat := [371285506390913174, 371285506174432503, 371285505957043667, 371285505934227436, 371285505827423004, 371285505694861578, 371285505561498453, 371285505405581533, 371285504983921570, 371285504680682758]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362466866438135481, 362466933636207845⟩, ⟨1248289053925298249, 1251347550019439451⟩, true⟩

def words08 : List Nat := [371285504376191225, 371285504254608239, 371285503949094619, 371285503643252731, 371285503336518565, 371285503097984093, 371285502781670812, 371285502662576209, 371285502542752691, 371285502378603148]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489138980798806, 362489206199703931⟩, ⟨(-252760682486268704), (-249700782373833338)⟩, true⟩

def words09 : List Nat := [371285502104626043, 371285502051824642, 371285502103527349, 371285502105829614, 371285501965470469, 371285501790550336, 371285501614685327, 371285501546074355, 371285501437713002, 371285501495287471]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk673B
