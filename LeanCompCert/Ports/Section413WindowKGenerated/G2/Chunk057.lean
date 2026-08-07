import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk057

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570848175899968, 360570848342737123⟩, ⟨11156399935456776, 11157045354585528⟩, true⟩

def state01 : KState := ⟨⟨360404896660542447, 360404896827992852⟩, ⟨958013867529949161, 958014516447791051⟩, true⟩

def words00 : List Nat := [360572835519922315, 360572835519987408, 360572835192768045, 360572819345153626, 360572803503085234, 360572765229393978, 360572742652993218, 360572728017411641, 360572713386950613, 360572675202151835]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360518512681683659, 360518512849751388⟩, ⟨309098147639090145, 309098800084927985⟩, true⟩

def words01 : List Nat := [360572646844791953, 360572647865202677, 360572663482816101, 360572663482881379, 360572648758405977, 360572607573385179, 360572566402760041, 360572560550290912, 360572560550344956, 360572551101514488]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360380992518478375, 360380992687168269⟩, ⟨1094980892592231078, 1094981548599983308⟩, true⟩

def words02 : List Nat := [360572541655977295, 360572516800189849, 360572461695843986, 360572421380502932, 360572381079228274, 360572331294323189, 360572283493526981, 360572215854848558, 360572148239770725, 360572088943468441]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360108320095232841, 360108320264540886⟩, ⟨2658651763028972414, 2658652422581853142⟩, true⟩

def words03 : List Nat := [360572055599209209, 360572025821850281, 360571996054874102, 360571941632533221, 360571873360601139, 360571787593263519, 360571701855806863, 360571646259517455, 360571580836449964, 360571500129102185]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360728091823009604, 360728091992937384⟩, ⟨(-901611444496558156), (-901610781383364732)⟩, true⟩

def words04 : List Nat := [360571419449854875, 360571368870706685, 360571348318872697, 360571353076541874, 360571353076602360, 360571331821941626, 360571315075496671, 360571296747674844, 360571290117846137, 360571317383063734]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360498909857492456, 360498910028046820⟩, ⟨417673550022178046, 417674216741426214⟩, true⟩

def words05 : List Nat := [360571327307481288, 360571337228455219, 360571350752967586, 360571388040634251, 360571417342416525, 360571446634029882, 360571456005352307, 360571456005418131, 360571435504050884, 360571422912897763]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360408239281534925, 360408239452710816⟩, ⟨939709000209780109, 939709670512203707⟩, true⟩

def words06 : List Nat := [360571410326094838, 360571396246122110, 360571369492317288, 360571322009767410, 360571274543679240, 360571219204337331, 360571180477219074, 360571159010655259, 360571137551525789, 360571100747426970]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574019651581499, 360574019823381053⟩, ⟨(-18534116532030753), (-18533442628093801)⟩, true⟩

def words07 : List Nat := [360571072526843847, 360571058934785108, 360571045347416071, 360571043572759309, 360571012111088668, 360570949485601152, 360570886881782110, 360570841881169836, 360570813345349266, 360570813900075727]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592206963798160, 360592207136228113⟩, ⟨(-124274116525901116), (-124273438975108780)⟩, true⟩

def words08 : List Nat := [360570813900134711, 360570794328053187, 360570796682962651, 360570812663435934, 360570812663491719, 360570810275567485, 360570805327254577, 360570785238413186, 360570765156500642, 360570747381613175]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360209787700641091, 360209787873695792⟩, ⟨2092791068440093062, 2092791749611300308⟩, true⟩

def words09 : List Nat := [360570780626461136, 360570813859843964, 360570831954674347, 360570831954740592, 360570820545669893, 360570792694430584, 360570764852779793, 360570723420335733, 360570676259488643, 360570614037421879]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk057
