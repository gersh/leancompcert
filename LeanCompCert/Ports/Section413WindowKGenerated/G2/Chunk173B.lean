import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173A

def state06 : KState := ⟨⟨360647205681532300, 360647207408470483⟩, ⟨(-1098337489690592153), (-1098317195641967039)⟩, true⟩

def words05 : List Nat := [360583938564063783, 360583942782163808, 360583945629304752, 360583945629524671, 360583945191436545, 360583941871151415, 360583938551207477, 360583936643866764, 360583940288674203, 360583943933115264]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554564703873629, 360554566432908568⟩, ⟨509998099415636672, 510018429874437180⟩, true⟩

def words06 : List Nat := [360583945894437415, 360583945894657495, 360583945430243853, 360583946288082141, 360583946288266758, 360583945254329525, 360583942876258625, 360583937912760127, 360583932949791419, 360583928461110896]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536899152082082, 360536900883189975⟩, ⟨817197109289216034, 817217475765735308⟩, true⟩

def words07 : List Nat := [360583926770999328, 360583926738328487, 360583926705637342, 360583925015652176, 360583925015836897, 360583923971776888, 360583925181100382, 360583925181320697, 360583924156783337, 360583921451415852]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360637068296890043, 360637070030080488⟩, ⟨(-924598285727488386), (-924577883046174332)⟩, true⟩

def words08 : List Nat := [360583918746312543, 360583914521345642, 360583912651830124, 360583913365171276, 360583913365374892, 360583911238951161, 360583905837751792, 360583903731688784, 360583902814035867, 360583905871432557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593675780543452, 360593677515833448⟩, ⟨(-169763238424013690), (-169742799221166222)⟩, true⟩

def words09 : List Nat := [360583906016550820, 360583906161674564, 360583909599432533, 360583915306755406, 360583918541737827, 360583921776381014, 360583923335160668, 360583923335381321, 360583922182293267, 360583922743163995]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173B
