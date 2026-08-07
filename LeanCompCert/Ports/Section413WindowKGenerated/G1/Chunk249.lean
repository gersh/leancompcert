import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk249

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476016652875068, 362476025110768650⟩, ⟨243331848161262912, 243474238023948294⟩, true⟩

def state01 : KState := ⟨⟨362460716053514058, 362460724518409222⟩, ⟨624405775868103620, 624548340106714844⟩, true⟩

def words00 : List Nat := [371285803669418754, 371285803670204741, 371285802392500554, 371285801125130128, 371285799857550712, 371285798759546630, 371285797077337983, 371285797007223578, 371285796936855810, 371285796711910094]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500184199748770, 362500192671766891⟩, ⟨(-359026457391655948), (-358883715684191906)⟩, true⟩

def words01 : List Nat := [371285795884757671, 371285796064486005, 371285796905406819, 371285796906193278, 371285795602015060, 371285793761716685, 371285791921254568, 371285791691285205, 371285791237648021, 371285791816436680]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491995861341955, 362492004340464657⟩, ⟨(-155010552800977562), (-154867634011646400)⟩, true⟩

def words02 : List Nat := [371285792358265014, 371285792359053846, 371285791796658652, 371285792320949069, 371285793318928402, 371285793319720587, 371285792953796116, 371285792284004537, 371285792240321170, 371285792490398008]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483295567179520, 362483304053378076⟩, ⟨62171071570791190, 62314166797509914⟩, true⟩

def words03 : List Nat := [371285794129907415, 371285795769598274, 371285797402355225, 371285798122846439, 371285799326932454, 371285800531316173, 371285802545645475, 371285802715315237, 371285802715911378, 371285802616601714]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484081889176860, 362484090382437495⟩, ⟨42657855603342132, 42801126993628874⟩, true⟩

def words04 : List Nat := [371285803079528653, 371285803080395857, 371285804212624592, 371285805582624128, 371285806711688741, 371285806712476264, 371285805701756900, 371285805311784028, 371285805857653306, 371285805858469304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464242267916969, 362464250768357344⟩, ⟨537903350697785674, 538046801258064782⟩, true⟩

def words05 : List Nat := [371285805790304806, 371285805716098958, 371285807172021040, 371285807903993923, 371285808552852160, 371285809201943367, 371285809666018002, 371285809666805871, 371285807993267254, 371285807130587235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473353158650786, 362473361666115954⟩, ⟨310549743603063503, 310693369538964969⟩, true⟩

def words06 : List Nat := [371285806790868760, 371285806791670260, 371285805987695168, 371285805112920427, 371285804237922282, 371285803847104146, 371285803565025024, 371285804226334254, 371285804331275543, 371285804332096690]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362530701499389967, 362530710013968725⟩, ⟨(-1121776157306864387), (-1121632353707952735)⟩, true⟩

def words07 : List Nat := [371285804939113157, 371285806044723860, 371285807810319457, 371285807811107869, 371285807441837669, 371285806695321118, 371285806803637792, 371285806999876404, 371285808797970695, 371285810596262951]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489861373603929, 362489869895309789⟩, ⟨(-101640485760192711), (-101496504090671165)⟩, true⟩

def words08 : List Nat := [371285812093324657, 371285812094113361, 371285811457340974, 371285811300230335, 371285811329412109, 371285811330205204, 371285810204568034, 371285809072830900, 371285808409635081, 371285808573070156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362455206330380352, 362455214859190299⟩, ⟨764739093477311514, 764883252714804804⟩, true⟩

def words09 : List Nat := [371285810060250611, 371285811547648333, 371285813045592819, 371285813046381724, 371285812412470944, 371285812261765528, 371285812616384719, 371285812617174445, 371285811412267350, 371285810189298892]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk249
