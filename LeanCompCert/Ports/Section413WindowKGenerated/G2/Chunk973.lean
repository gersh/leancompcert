import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973

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

def state06 : KState := ⟨⟨360556783579207924, 360556846267683237⟩, ⟨2483003931138228091, 2487125146018908617⟩, true⟩

def words05 : List Nat := [360582392590636182, 360582392686547039, 360582392715372480, 360582392716785769, 360582392640355648, 360582392537587447, 360582392434380840, 360582392362547710, 360582392185405871, 360582391924482939]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573482654718688, 360573545356551516⟩, ⟨857011290488895025, 861133805922776259⟩, true⟩

def words06 : List Nat := [360582391663252772, 360582391391228762, 360582391174103490, 360582390952812627, 360582390731416355, 360582390420734372, 360582390032429356, 360582389749982468, 360582389467126209, 360582389290062072]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570600996767521, 360570663712066957⟩, ⟨1137612541459792836, 1141736368204231308⟩, true⟩

def words07 : List Nat := [360582389200507027, 360582389049876652, 360582388898968785, 360582388859749207, 360582388860936659, 360582388801893652, 360582388742715747, 360582388602328617, 360582388377648631, 360582388258875380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582778703584301, 360582841432191901⟩, ⟨(-48307226099529160), (-44182103338868196)⟩, true⟩

def words08 : List Nat := [360582388139619365, 360582388126055033, 360582388119183892, 360582388021009821, 360582387922581144, 360582387797795525, 360582387756533424, 360582387789445400, 360582387790717974, 360582387775248869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605451591544088, 360605514333522656⟩, ⟨(-2256604712313572654), (-2252478287289413532)⟩, true⟩

def words09 : List Nat := [360582387778682177, 360582387782510781, 360582387814634786, 360582387875503942, 360582387876808475, 360582387843311142, 360582387879997970, 360582388033033288, 360582388271612601, 360582388510509654]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk973
