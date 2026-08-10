import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk784A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk784B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk784A

def state06 : KState := ⟨⟨362469347149131936, 362469439321170236⟩, ⟨1235002989099478687, 1239886468149305709⟩, true⟩

def words05 : List Nat := [371285242660694479, 371285242764158258, 371285242852693924, 371285242855401817, 371285242727345013, 371285242607262345, 371285242500709870, 371285242503417910, 371285242304020353, 371285242105622815]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475790909684669, 362475883106001061⟩, ⟨729384853449182693, 734270237480833291⟩, true⟩

def words06 : List Nat := [371285241906051645, 371285241843374854, 371285241698011942, 371285241571401597, 371285241443912345, 371285241290761616, 371285240920355148, 371285240713624277, 371285240505508754, 371285240443040450]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477891452742599, 362477983673781029⟩, ⟨564568259316948010, 569455583407127910⟩, true⟩

def words07 : List Nat := [371285240325838532, 371285240208954686, 371285240105709895, 371285240108719207, 371285240095319771, 371285240109191074, 371285240111252810, 371285240075593021, 371285239822744772, 371285239733712313]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468470095268534, 362468562340420708⟩, ⟨1304003834110520158, 1308893050774192024⟩, true⟩

def words08 : List Nat := [371285239657953542, 371285239660662755, 371285239461242881, 371285239262775791, 371285239063262866, 371285238869174135, 371285238600871555, 371285238495885898, 371285238389995057, 371285238261567023]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487650450226511, 362487742719891381⟩, ⟨(-201577642472804556), (-196686501685863220)⟩, true⟩

def words09 : List Nat := [371285238050980523, 371285237909137511, 371285237765920695, 371285237761517593, 371285237601276821, 371285237415727395, 371285237229021297, 371285237205691097, 371285237156337592, 371285237191277913]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk784B
