import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569316458625669, 360569378666526364⟩, ⟨1256296837518573759, 1260371350142082897⟩, true⟩

def state01 : KState := ⟨⟨360609588902733199, 360609651123921939⟩, ⟨(-2650302776536880680), (-2646226974908034238)⟩, true⟩

def words00 : List Nat := [360582372052785527, 360582372072790958, 360582372226310616, 360582372380096997, 360582372435504990, 360582372554037704, 360582372778554404, 360582373003481098, 360582373244153573, 360582373526794727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594114582047255, 360594176816685065⟩, ⟨(-1149032658680752995), (-1144955552297209411)⟩, true⟩

def words01 : List Nat := [360582373755743781, 360582373984829034, 360582374211102822, 360582374522833996, 360582374807103271, 360582375091596723, 360582375317851702, 360582375459994679, 360582375582779846, 360582375706077082]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592212639396994, 360592274887267938⟩, ⟨(-964495074932131710), (-960416684602188994)⟩, true⟩

def words02 : List Nat := [360582375935106327, 360582376081866993, 360582376175077184, 360582376268439243, 360582376334789325, 360582376465454811, 360582376575929099, 360582376686651126, 360582376744155748, 360582376847624915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613911081926158, 360613973343093698⟩, ⟨(-3070052975252373293), (-3065973294687954479)⟩, true⟩

def words03 : List Nat := [360582376966950925, 360582377086687836, 360582377252719531, 360582377457187844, 360582377571631085, 360582377686185437, 360582377850692293, 360582378071639401, 360582378398367994, 360582378725409545]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606367312010224, 360606429586604238⟩, ⟨(-2338042733052821498), (-2333961749516396394)⟩, true⟩

def words04 : List Nat := [360582378970600826, 360582379203616121, 360582379510219645, 360582379817230310, 360582380066328381, 360582380209811832, 360582380285064729, 360582380360482161, 360582380520085413, 360582380769492448]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578261880532378, 360578324168391245⟩, ⟨389718604925257619, 393800875881603339⟩, true⟩

def words05 : List Nat := [360582381028537943, 360582381287849945, 360582381450165543, 360582381506798980, 360582381507999176, 360582381476499509, 360582381487694135, 360582381500656077, 360582381501911162, 360582381461569502]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591480672072663, 360591542973244533⟩, ⟨(-893347877242813542), (-889264314060222954)⟩, true⟩

def words06 : List Nat := [360582381425314645, 360582381513555069, 360582381658589834, 360582381803900281, 360582381858496003, 360582381859904934, 360582381842954880, 360582381878933682, 360582381909516969, 360582382005354430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585683584316607, 360585745898901154⟩, ⟨(-330594566526628547), (-326509701307961913)⟩, true⟩

def words07 : List Nat := [360582382023377093, 360582382041544500, 360582382165573535, 360582382343911757, 360582382449899675, 360582382556130506, 360582382608865959, 360582382610275059, 360582382591758930, 360582382628010785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588378073114796, 360588440400993388⟩, ⟨(-592233333797322040), (-588147177927963274)⟩, true⟩

def words08 : List Nat := [360582382769906371, 360582382806294177, 360582382807585511, 360582382749836015, 360582382691851095, 360582382607223637, 360582382635027965, 360582382667806130, 360582382669061524, 360582382711012567]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593356293041498, 360593418634215845⟩, ⟨(-1075583314374627503), (-1071495867555339589)⟩, true⟩

def words09 : List Nat := [360582382854267296, 360582382997951550, 360582383226928675, 360582383388064728, 360582383459302325, 360582383530648485, 360582383531821257, 360582383545079602, 360582383659865613, 360582383774970778]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970
