import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk663

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588080928552659, 360588109137234412⟩, ⟨(-343185088505170853), (-341921743493861491)⟩, true⟩

def state01 : KState := ⟨⟨360590160869414529, 360590189086895765⟩, ⟨(-481126447570283951), (-479862519109360057)⟩, true⟩

def words00 : List Nat := [360582952329886294, 360582952408617207, 360582952409458264, 360582952356966236, 360582952304306687, 360582952153487810, 360582952287747009, 360582952435638894, 360582952436473837, 360582952542142868]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584760616548665, 360584788842868980⟩, ⟨(-123056616601963540), (-121792101977661356)⟩, true⟩

def words01 : List Nat := [360582952647126920, 360582952752379526, 360582952924710148, 360582952935960716, 360582952936823137, 360582952754096680, 360582952571198883, 360582952389708226, 360582952410930205, 360582952439588305]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569733576664587, 360569761811896277⟩, ⟨873468514228245171, 874733619898474643⟩, true⟩

def words02 : List Nat := [360582952440429365, 360582952354592355, 360582952041678830, 360582951851680156, 360582951661453973, 360582951312813730, 360582950898307813, 360582950370373424, 360582949842277501, 360582949413583274]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559764453373341, 360559792697421274⟩, ⟨1534842454692994600, 1536108145187808636⟩, true⟩

def words03 : List Nat := [360582949215524497, 360582949199049246, 360582949182454857, 360582949052473585, 360582948848009003, 360582948587045091, 360582948325814632, 360582948291517528, 360582948127574011, 360582947779501284]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595023969946404, 360595052222819169⟩, ⟨(-804499929773367450), (-803233653794874888)⟩, true⟩

def words04 : List Nat := [360582947431231880, 360582947031126326, 360582946744742868, 360582946685265057, 360582946625716318, 360582946372494137, 360582946126794344, 360582946108089974, 360582946213503081, 360582946396926645]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360574468419674828, 360574496681471271⟩, ⟨559430856803468869, 560697724911722027⟩, true⟩

def words05 : List Nat := [360582946421734364, 360582946446652699, 360582946466540845, 360582946600591877, 360582946609872013, 360582946619303600, 360582946620145240, 360582946493723480, 360582946140517648, 360582946014275848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553545464603885, 360553573735209452⟩, ⟨1947987655886531990, 1949255108613647740⟩, true⟩

def words06 : List Nat := [360582945987006017, 360582945987941751, 360582945861480365, 360582945561659293, 360582945261698139, 360582944837052940, 360582944527733689, 360582944141710445, 360582943755594178, 360582943256207097]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608712774771995, 360608741054210823⟩, ⟨(-1713772431213822066), (-1712504392180138340)⟩, true⟩

def words07 : List Nat := [360582942814459075, 360582942510732180, 360582942206739933, 360582942172991205, 360582942173863630, 360582942011116670, 360582941911048052, 360582942164400094, 360582942553811728, 360582942943423397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593242455247439, 360593270743610517⟩, ⟨(-686932509970671244), (-685663878500611846)⟩, true⟩

def words08 : List Nat := [360582943145167185, 360582943146103299, 360582943322192468, 360582943524134341, 360582943524925378, 360582943515132598, 360582943406224609, 360582943184118408, 360582942961823399, 360582943080546238]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556778241351091, 360556806538525135⟩, ⟨1734154190424146879, 1735423406898457549⟩, true⟩

def words09 : List Nat := [360582943304080014, 360582943527783143, 360582943638276386, 360582943639212797, 360582943585235012, 360582943372007268, 360582943158504492, 360582943105405114, 360582942825855699, 360582942433207341]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk663
