import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563289449207146, 360563352057472515⟩, ⟨1848499811163379269, 1852613219214054241⟩, true⟩

def state01 : KState := ⟨⟨360585013635599050, 360585076257194321⟩, ⟨(-265326438269805748), (-261211733154003972)⟩, true⟩

def words00 : List Nat := [360582392081010857, 360582391992481028, 360582392024146818, 360582392093615863, 360582392094924804, 360582392073457104, 360582392035522322, 360582391995589058, 360582391955222432, 360582391959086667]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591937079019864, 360591999714065421⟩, ⟨(-939110368014011177), (-934994353984147159)⟩, true⟩

def words01 : List Nat := [360582391960345234, 360582391931603620, 360582391922443057, 360582392027053969, 360582392104452578, 360582392182080178, 360582392183359250, 360582392190128809, 360582392289991758, 360582392390322507]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582710052528065, 360582772700891110⟩, ⟨(-41151218113164274), (-37033907957043434)⟩, true⟩

def words02 : List Nat := [360582392487804400, 360582392489217291, 360582392481560140, 360582392421090305, 360582392360394543, 360582392233456124, 360582392190179569, 360582392222183947, 360582392223442638, 360582392206413945]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585970152953513, 360586032814648129⟩, ⟨(-358475915072620291), (-354357307289249009)⟩, true⟩

def words03 : List Nat := [360582392242556922, 360582392279108777, 360582392400020334, 360582392459089616, 360582392460429257, 360582392418027529, 360582392375356686, 360582392366711163, 360582392405260417, 360582392444122973]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584234249168091, 360584296924341673⟩, ⟨(-189518021248798980), (-185398101357442338)⟩, true⟩

def words04 : List Nat := [360582392445381987, 360582392446229885, 360582392558650446, 360582392671505987, 360582392757198481, 360582392758611680, 360582392739200842, 360582392652080716, 360582392564711494, 360582392494994698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973A
