import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk610

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476889317262862, 362476943946456008⟩, ⟨507945697536855922, 510196618258225234⟩, true⟩

def state01 : KState := ⟨⟨362498207254484447, 362498261902177219⟩, ⟨(-792487785316554083), (-790235736024049513)⟩, true⟩

def words00 : List Nat := [371285307821708349, 371285307824007632, 371285308050668719, 371285308280379329, 371285308455501668, 371285308457584303, 371285308698286026, 371285308954942318, 371285309339210531, 371285309553649511]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479348106418605, 362479402772954360⟩, ⟨358261263666028645, 360514462664533733⟩, true⟩

def words01 : List Nat := [371285309768264229, 371285309983575406, 371285310290819472, 371285310465138602, 371285310719248468, 371285310974162109, 371285311166802408, 371285311168870348, 371285311003280021, 371285310909019004]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486416973494721, 362486471658458208⟩, ⟨(-73091681286705630), (-70837357732153940)⟩, true⟩

def words02 : List Nat := [371285310964665677, 371285310966743596, 371285310863041821, 371285310759121851, 371285310654386232, 371285310633791029, 371285310660355329, 371285310809604234, 371285310958986638, 371285310980151575]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498599450400804, 362498654154100603⟩, ⟨(-816623343389004283), (-814367876261948785)⟩, true⟩

def words03 : List Nat := [371285311269392089, 371285311559712993, 371285311959054219, 371285312001112923, 371285312017801755, 371285312035107738, 371285312277783189, 371285312387220742, 371285312607208723, 371285312828167838]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485183130759097, 362485237853111199⟩, ⟨2347882106559277, 4604487865304797⟩, true⟩

def words04 : List Nat := [371285313047382393, 371285313049454190, 371285313179752744, 371285313380998789, 371285313629999403, 371285313632068485, 371285313552531247, 371285313392793586, 371285313272318360, 371285313274697855]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487667911756009, 362487722652699100⟩, ⟨(-149276993208026762), (-147019252375753820)⟩, true⟩

def words05 : List Nat := [371285313542275767, 371285313811903088, 371285314070496564, 371285314121457606, 371285314252311348, 371285314384238026, 371285314783634186, 371285314826046175, 371285314867026594, 371285314908764744]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492103601940851, 362492158361423580⟩, ⟨(-420169344862868795), (-417910471905508101)⟩, true⟩

def words06 : List Nat := [371285314940468376, 371285314942748481, 371285314969671736, 371285315100805285, 371285315153721383, 371285315155795371, 371285314946951189, 371285314964066260, 371285315220718786, 371285315334915000]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494281467287775, 362494336245638037⟩, ⟨(-553149899391006499), (-550889874098796893)⟩, true⟩

def words07 : List Nat := [371285315447620199, 371285315561062883, 371285315914312147, 371285316188254860, 371285316465833971, 371285316744150689, 371285317020920983, 371285317022990903, 371285317089910973, 371285317240151899]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478545256814381, 362478600053625030⟩, ⟨408140442444245906, 410401595393483522⟩, true⟩

def words08 : List Nat := [371285317557778065, 371285317654072894, 371285317696755847, 371285317740092511, 371285317846675213, 371285317848956129, 371285317908140104, 371285317996626085, 371285318034708969, 371285318036852948]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362517292252586856, 362517347068092223⟩, ⟨(-1959100892338052965), (-1956838597233367277)⟩, true⟩

def words09 : List Nat := [371285318086578468, 371285318247338526, 371285318659365159, 371285318832435698, 371285318964297934, 371285319096858148, 371285319463606391, 371285319721902524, 371285320247486275, 371285320773968832]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk610
