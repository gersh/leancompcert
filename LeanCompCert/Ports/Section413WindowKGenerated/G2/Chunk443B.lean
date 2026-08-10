import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443A

def state06 : KState := ⟨⟨360586255935891615, 360586268159939800⟩, ⟨(-133585407016098704), (-133218959385519382)⟩, true⟩

def words05 : List Nat := [360583266775285576, 360583266685929112, 360583266674032036, 360583266674638318, 360583266421377463, 360583265737930071, 360583265054394587, 360583264958575005, 360583265026774300, 360583265095099388]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560031672349657, 360560043902178093⟩, ⟨1029643135250496138, 1030009839320314312⟩, true⟩

def words06 : List Nat := [360583265095645484, 360583264853200451, 360583264329477551, 360583263701471869, 360583263073335179, 360583262210524697, 360583261365031431, 360583260196862870, 360583259028632898, 360583258007188693]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360537499565250749, 360537511800793695⟩, ⟨2029634891823399421, 2030001849475288503⟩, true⟩

def words07 : List Nat := [360583257484497129, 360583257469248554, 360583257453943771, 360583257046678247, 360583256567391440, 360583255902740373, 360583255237941365, 360583254971070537, 360583254197448298, 360583253167388452]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577112936330151, 360577125177598030⟩, ⟨271464637149999561, 271831848902563615⟩, true⟩

def words08 : List Nat := [360583252137226880, 360583251614382554, 360583251733414071, 360583252046816387, 360583252047379421, 360583251855276469, 360583251156478743, 360583250233952682, 360583249311283581, 360583248895753078]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572909631898630, 360572921878942873⟩, ⟨458099039339868138, 458466507533698848⟩, true⟩

def words09 : List Nat := [360583248758344027, 360583248366333038, 360583247974223125, 360583248346222664, 360583248461082917, 360583248576038650, 360583248576584236, 360583248435288116, 360583247933060429, 360583247701184623]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443B
