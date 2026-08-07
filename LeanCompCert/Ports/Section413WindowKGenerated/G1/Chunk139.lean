import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk139

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362419756879909111, 362419759384709892⟩, ⟨901409669403563286, 901433224691920734⟩, true⟩

def state01 : KState := ⟨⟨362522725852503417, 362522728361049945⟩, ⟨(-530059616085168652), (-530036008711896618)⟩, true⟩

def words00 : List Nat := [371284606534158542, 371284606534626126, 371284608864840977, 371284612613205702, 371284615446072202, 371284615446491121, 371284615941478317, 371284618771581231, 371284623687091901, 371284626426702171]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362516185687878646, 362516188200236889⟩, ⟨(-438896836193057747), (-438873175779909381)⟩, true⟩

def words01 : List Nat := [371284629152156506, 371284631877363555, 371284639761698182, 371284645089832402, 371284649963762866, 371284654837153961, 371284659698851874, 371284659699270070, 371284659954327154, 371284662219647858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494856563800931, 362494859079889144⟩, ⟨(-141846318049833098), (-141822605695908592)⟩, true⟩

def words02 : List Nat := [371284669637143132, 371284670186601087, 371284670186924683, 371284669712824495, 371284670167903363, 371284670168366939, 371284672216723353, 371284675106220514, 371284677987869746, 371284678719132852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362567270548151644, 362567273068019455⟩, ⟨(-1150762079324951884), (-1150738314302354684)⟩, true⟩

def words03 : List Nat := [371284684593774409, 371284690467788847, 371284701483646164, 371284705642624065, 371284708919327280, 371284712195697538, 371284716066895762, 371284717768156526, 371284723690629278, 371284729612435039]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489586955206771, 362489589478859227⟩, ⟨(-67562623625440547), (-67538805825731221)⟩, true⟩

def words04 : List Nat := [371284735514386710, 371284735514805732, 371284738104553774, 371284741641020641, 371284746765522404, 371284746765942394, 371284746669377574, 371284746566460015, 371284747986919463, 371284748334437628]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362415179123429791, 362415181650863209⟩, ⟨970969242621435357, 970993113185289241⟩, true⟩

def words05 : List Nat := [371284750762173616, 371284753189732295, 371284755612503676, 371284755612923016, 371284751200939865, 371284748380893964, 371284745889423346, 371284745889849946, 371284742013823580, 371284737031463875]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362504690605177296, 362504693136367349⟩, ⟨(-278939737234166886), (-278915814208647958)⟩, true⟩

def words06 : List Nat := [371284732049629199, 371284730634685339, 371284729189415218, 371284731025149863, 371284731957816512, 371284731958236254, 371284726068922125, 371284725294170167, 371284727794898683, 371284729224391926]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499940816170445, 362499943351182621⟩, ⟨(-212359676287107030), (-212335699846634080)⟩, true⟩

def words07 : List Nat := [371284730654465121, 371284732084478704, 371284737756823592, 371284741363961689, 371284745821014834, 371284750277592140, 371284754718674121, 371284754719094688, 371284754817059512, 371284755903943752]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362432635091397394, 362432637630157081⟩, ⟨728823118096301692, 728847146946110268⟩, true⟩

def words08 : List Nat := [371284758390933860, 371284758391354280, 371284754072655576, 371284749401613065, 371284744731071066, 371284741656091431, 371284736762796290, 371284736292205121, 371284735821541598, 371284735353312629]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506547849706792, 362506550392276523⟩, ⟨(-305766918357731804), (-305742836186320298)⟩, true⟩

def words09 : List Nat := [371284731629939539, 371284731061506103, 371284732001638851, 371284732002059567, 371284726718959046, 371284720644352370, 371284714570447165, 371284713584451759, 371284711617776987, 371284713178064230]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk139
