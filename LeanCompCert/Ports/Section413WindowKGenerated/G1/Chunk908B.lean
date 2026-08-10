import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908A

def state06 : KState := ⟨⟨362486206450906255, 362486331463710835⟩, ⟨(-118163938938531542), (-110494799083705940)⟩, true⟩

def words05 : List Nat := [371285115596895463, 371285115634877686, 371285115721737209, 371285115724909232, 371285115650631774, 371285115560343123, 371285115468747549, 371285115431941127, 371285115360606133, 371285115377611368]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475168658718949, 362475293700118060⟩, ⟨884755175694745032, 892426913795662888⟩, true⟩

def words06 : List Nat := [371285115393599664, 371285115396772263, 371285115262232844, 371285115250457278, 371285115237039157, 371285115235682754, 371285115072178251, 371285114885991539, 371285114698546049, 371285114619165003]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467398628798009, 362467523698770168⟩, ⟨1590893427099401016, 1598567761778899826⟩, true⟩

def words07 : List Nat := [371285114513255888, 371285114469983693, 371285114425636166, 371285114373092630, 371285114218776234, 371285114101673660, 371285113982966650, 371285113953980040, 371285113762849236, 371285113572909461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477021749757817, 362477146848178810⟩, ⟨716301163468288735, 723978083720157861⟩, true⟩

def words08 : List Nat := [371285113381550282, 371285113241990869, 371285113065296156, 371285112970653287, 371285112875053487, 371285112768493557, 371285112529781007, 371285112413780635, 371285112296041749, 371285112279840381]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470822715205130, 362470947842530280⟩, ⟨1279777647573803806, 1287457195067028198⟩, true⟩

def words09 : List Nat := [371285112194597427, 371285112110570599, 371285112025294223, 371285112003231304, 371285111919507806, 371285111840323914, 371285111759999535, 371285111670000153, 371285111439897634, 371285111288020567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk908B
