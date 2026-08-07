import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk018

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362574485098685243, 362574485132989556⟩, ⟨(-183719214831869784), (-183719172858217184)⟩, true⟩

def state01 : KState := ⟨⟨362509192126568383, 362509192161271190⟩, ⟨(-63864696565090722), (-63864653872056626)⟩, true⟩

def words00 : List Nat := [371272838538908859, 371272917299510308, 371272989307221943, 371273061235161376, 371273205622525259, 371273244251422635, 371273473017237861, 371273701530151765, 371273907822069021, 371273927305461110]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362717678595561868, 362717678630671113⟩, ⟨(-441644745794381199), (-441644702363603029)⟩, true⟩

def words01 : List Nat := [371274249751495324, 371274571841847420, 371274978734711128, 371274984385037843, 371274984385072897, 371274898473605094, 371274922645780502, 371274922645830372, 371275016706244523, 371275149963804775]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362335020714751627, 362335020750268288⟩, ⟨255491555748085349, 255491599922462371⟩, true⟩

def words02 : List Nat := [371275279073169756, 371275279073214934, 371275041923186944, 371275072477175137, 371275188019397058, 371275188019442576, 371275056245872428, 371274846551110232, 371274637085630266, 371274633646400782]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362111376375443513, 362111376411370618⟩, ⟨669247935831672605, 669247980759276019⟩, true⟩

def words03 : List Nat := [371274776743979323, 371274995851778862, 371275204621070121, 371275204621116410, 371275238356443192, 371275296886519327, 371275491426524819, 371275491426570470, 371275295922335403, 371275098140044138]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473656244075311, 362473656280413004⟩, ⟨670755900021239, 670801585211017⟩, true⟩

def words04 : List Nat := [371274900572596916, 371274817221126878, 371274590097901133, 371274543923855763, 371274497799850249, 371274385414914385, 371274014863451046, 371273934622134516, 371274018875816992, 371274018875864470]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362002119284942675, 362002119321698547⟩, ⟨877211908157086373, 877211954618068037⟩, true⟩

def words05 : List Nat := [371274018680007255, 371274016967883770, 371274186044352009, 371274217248878663, 371274256316360593, 371274295341784138, 371274334268880048, 371274334268926105, 371273992347257224, 371273738652138369]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362295973532283244, 362295973569451185⟩, ⟨330582986077075225, 330583033306684757⟩, true⟩

def words06 : List Nat := [371273517214725389, 371273517214772406, 371273360639581217, 371273182692845172, 371273004936918898, 371272910265251451, 371272721284704780, 371272768626111088, 371272768626146371, 371272755940203423]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨363362010565067092, 363362010602655859⟩, ⟨(-1668152497940948398), (-1668152449922254486)⟩, true⟩

def words07 : List Nat := [371272849728101007, 371273037800484250, 371273508031097333, 371273602648975391, 371273652040126387, 371273701378664405, 371274031922844980, 371274223242314780, 371274695469665869, 371275167194935363]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362621433895139253, 362621433933151225⟩, ⟨(-275102860726006018), (-275102811909524890)⟩, true⟩

def words08 : List Nat := [371275583124717341, 371275626281259409, 371275777723311944, 371275929004706082, 371276110444674166, 371276110444721125, 371276023762421633, 371275881789240375, 371275876889758218, 371275953863394734]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362196718158010803, 362196718196445651⟩, ⟨531527775926325637, 531527825544237697⟩, true⟩

def words09 : List Nat := [371276231339113958, 371276508521692222, 371276783333236822, 371276783333283897, 371276690249093964, 371276677477868723, 371276760792286505, 371276760792333876, 371276616998680771, 371276469683574198]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk018
