import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598133878283773, 360598190493696106⟩, ⟨(-1504611486062987237), (-1501067517769400087)⟩, true⟩

def state01 : KState := ⟨⟨360584422218225893, 360584478846282771⟩, ⟨(-233582016522731911), (-230036876016868617)⟩, true⟩

def words00 : List Nat := [360581998004364310, 360581998005705318, 360581997971309939, 360581997863510521, 360581997755494600, 360581997618763479, 360581997575869816, 360581997613372122, 360581997614578087, 360581997621012665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594985946373454, 360595042587091669⟩, ⟨(-1213026025417743961), (-1209479711017994385)⟩, true⟩

def words01 : List Nat := [360581997740347878, 360581997860074460, 360581997979642536, 360581998010087981, 360581998011346482, 360581997931915671, 360581997887656723, 360581998012179573, 360581998153958921, 360581998296035512]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593224210804797, 360593280864309544⟩, ⟨(-1049678465032118326), (-1046130965001815708)⟩, true⟩

def words02 : List Nat := [360581998372360139, 360581998485956017, 360581998715463857, 360581998945360846, 360581999145034064, 360581999261819960, 360581999320670235, 360581999379654651, 360581999390052257, 360581999513251087]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576363991095254, 360576420657222043⟩, ⟨513890488186029609, 517439158722701515⟩, true⟩

def words03 : List Nat := [360581999714785057, 360581999916571684, 360582000059837752, 360582000108367003, 360582000109492671, 360582000089879692, 360582000164861111, 360582000175211593, 360582000176409369, 360582000117635271]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594089704708335, 360594146383515468⟩, ⟨(-1130135224260959815), (-1126585377689434311)⟩, true⟩

def words04 : List Nat := [360582000058565336, 360582000065080323, 360582000111108411, 360582000157373873, 360582000158624138, 360582000102375914, 360581999961991813, 360581999913426411, 360581999909025303, 360582000041398516]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360585271111785402, 360585327803370698⟩, ⟨(-312137564012652109), (-308586532202729591)⟩, true⟩

def words05 : List Nat := [360582000104650579, 360582000168061176, 360582000347318690, 360582000585620405, 360582000758148252, 360582000930886093, 360582001013540020, 360582001045050440, 360582001082001421, 360582001119395723]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585432355539966, 360585489059755458⟩, ⟨(-327112030145957577), (-323559826693262895)⟩, true⟩

def words06 : List Nat := [360582001272449059, 360582001309849225, 360582001311064116, 360582001258756889, 360582001206208362, 360582001124961041, 360582001192657497, 360582001285355866, 360582001294792865, 360582001333777585]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603227979654944, 360603284696553398⟩, ⟨(-1978176738835541370), (-1974623358721213990)⟩, true⟩

def words07 : List Nat := [360582001335494042, 360582001337600131, 360582001433762131, 360582001512179949, 360582001513419098, 360582001493046655, 360582001494074875, 360582001608912079, 360582001839389887, 360582002070167380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592518408081170, 360592575137767262⟩, ⟨(-984605623253168618), (-981051056638452632)⟩, true⟩

def words08 : List Nat := [360582002221254504, 360582002318833993, 360582002429595718, 360582002540747993, 360582002544157885, 360582002545503819, 360582002509555689, 360582002410234037, 360582002326041158, 360582002441529066]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583223507289569, 360583280249638322⟩, ⟨(-122004355306942035), (-118448613662473715)⟩, true⟩

def words09 : List Nat := [360582002672594911, 360582002903936580, 360582003076790491, 360582003256626842, 360582003390902801, 360582003525545845, 360582003744218493, 360582003847338950, 360582003862322613, 360582003877469246]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927
