import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk827

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360600485622591552, 360600530284929237⟩, ⟨(-1503238168353879860), (-1500743710514148512)⟩, true⟩

def state01 : KState := ⟨⟨360578894975885563, 360578939649524097⟩, ⟨282346763500214453, 284842155974944085⟩, true⟩

def words00 : List Nat := [360582383810169104, 360582383811354753, 360582383930337948, 360582384050253665, 360582384051266016, 360582384035447031, 360582383977167354, 360582383829288918, 360582383681189899, 360582383515513397]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556407636764963, 360556452321583642⟩, ⟨2142443675019014580, 2144939992258468700⟩, true⟩

def words01 : List Nat := [360582383549774537, 360582383625919411, 360582383626976099, 360582383619264411, 360582383465558235, 360582383252299187, 360582383038696796, 360582382947462921, 360582382759451364, 360582382447215394]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610588461526663, 360610633157530245⟩, ⟨(-2339660075118118573), (-2337162832607047433)⟩, true⟩

def words02 : List Nat := [360582382134709325, 360582381968648197, 360582381987851335, 360582382071199337, 360582382072294509, 360582382044870142, 360582382204034517, 360582382363556875, 360582382668781449, 360582383011483334]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585620567038961, 360585665274357311⟩, ⟨(-273944995784002865), (-271446817148037263)⟩, true⟩

def words03 : List Nat := [360582383233219759, 360582383455078255, 360582383638868907, 360582383896034912, 360582384116169170, 360582384336491668, 360582384466447637, 360582384511830586, 360582384552444418, 360582384593471801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580967879219458, 360581012597704014⟩, ⟨111058536184448446, 113557638769289436⟩, true⟩

def words04 : List Nat := [360582384739699862, 360582384863772646, 360582384914421528, 360582384965198601, 360582384966198549, 360582384926895015, 360582384940326936, 360582384953969230, 360582384955026385, 360582384895453492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360617831588896998, 360617876318579736⟩, ⟨(-2939648823230805020), (-2937148793940780516)⟩, true⟩

def words05 : List Nat := [360582384975599148, 360582385072674293, 360582385191541171, 360582385363125777, 360582385409095782, 360582385455148840, 360582385646922613, 360582385931129540, 360582386360923818, 360582386790976871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608980127736760, 360609024868734031⟩, ⟨(-2207166995622497091), (-2204666029888188347)⟩, true⟩

def words06 : List Nat := [360582387105464465, 360582387274425588, 360582387589093556, 360582387904126500, 360582388182165705, 360582388384327875, 360582388499933201, 360582388615685551, 360582388815308387, 360582389138467535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561042892279190, 360561087644445939⟩, ⟨1760886658038474913, 1763388548327086551⟩, true⟩

def words07 : List Nat := [360582389505017611, 360582389871781718, 360582390133679394, 360582390250104017, 360582390251122967, 360582390224027159, 360582390196585233, 360582390175712643, 360582390009135230, 360582389753026842]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598801742563556, 360598846505955412⟩, ⟨(-1364954344591503820), (-1362451525035129734)⟩, true⟩

def words08 : List Nat := [360582389496655435, 360582389389215991, 360582389457281905, 360582389525577264, 360582389526672015, 360582389470756995, 360582389558088593, 360582389675509525, 360582389788633883, 360582389988640304]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595165081715776, 360595209856420023⟩, ⟨(-1063844091854522969), (-1061340335689262683)⟩, true⟩

def words09 : List Nat := [360582390115269143, 360582390242014671, 360582390514367178, 360582390860015777, 360582391136666209, 360582391413523481, 360582391569106429, 360582391579283325, 360582391735053156, 360582391891230119]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk827
