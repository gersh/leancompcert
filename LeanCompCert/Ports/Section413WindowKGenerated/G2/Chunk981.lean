import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604700932841693, 360604764615290713⟩, ⟨(-2193781293044900054), (-2189562936666506820)⟩, true⟩

def state01 : KState := ⟨⟨360593555467910038, 360593619163761044⟩, ⟨(-1100337906578848525), (-1096118235396391143)⟩, true⟩

def words00 : List Nat := [360582445471584071, 360582445720845154, 360582445910860122, 360582446101026526, 360582446220452434, 360582446395120178, 360582446564130461, 360582446733406370, 360582446822713850, 360582446938063657]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595779608904204, 360595843318231645⟩, ⟨(-1318573097202119662), (-1314352103782110926)⟩, true⟩

def words01 : List Nat := [360582447083914349, 360582447230202829, 360582447438509761, 360582447543516220, 360582447560978174, 360582447578552751, 360582447666982786, 360582447825365077, 360582447963058914, 360582448101063230]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607396857915672, 360607460580804388⟩, ⟨(-2458616454962222953), (-2454394130843322579)⟩, true⟩

def words02 : List Nat := [360582448186786071, 360582448198411796, 360582448313566047, 360582448429149320, 360582448511177013, 360582448626507336, 360582448689684327, 360582448753003730, 360582448919840195, 360582449176346640]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575917534376600, 360575981270706104⟩, ⟨630632100016995410, 634855743148142032⟩, true⟩

def words03 : List Nat := [360582449445776842, 360582449715466955, 360582449905083274, 360582450013607164, 360582450073631868, 360582450134047599, 360582450224862581, 360582450226288125, 360582450213692968, 360582450149279043]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590548236670868, 360590611986453522⟩, ⟨(-805313230071439321), (-801088266582350471)⟩, true⟩

def words04 : List Nat := [360582450084522021, 360582450006296428, 360582450110455251, 360582450215264816, 360582450231259031, 360582450232685786, 360582450185990368, 360582450135762666, 360582450107571094, 360582450192212177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360591448639383284, 360591512402737989⟩, ⟨(-893712545120421143), (-889486249468530671)⟩, true⟩

def words05 : List Nat := [360582450224603783, 360582450257150427, 360582450305291927, 360582450445953826, 360582450547157886, 360582450648592799, 360582450697849470, 360582450711784872, 360582450805252887, 360582450899193114]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576832037683856, 360576895814480085⟩, ⟨541059957598754900, 545287572738762800⟩, true⟩

def words06 : List Nat := [360582450962255987, 360582450963681865, 360582450923389567, 360582450817112633, 360582450710594372, 360582450559023195, 360582450458797124, 360582450438937706, 360582450418898658, 360582450337987662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591403521685713, 360591467311943836⟩, ⟨(-889531520161402416), (-885302583402922214)⟩, true⟩

def words07 : List Nat := [360582450308864325, 360582450336755891, 360582450409820735, 360582450411246830, 360582450403116091, 360582450278478437, 360582450153563731, 360582450091567191, 360582450172726538, 360582450266044906]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585159211649901, 360585223015515351⟩, ⟨(-276450364462389697), (-272220091668078061)⟩, true⟩

def words08 : List Nat := [360582450307250467, 360582450350738505, 360582450464908436, 360582450579494658, 360582450652941885, 360582450710713874, 360582450711986216, 360582450702240915, 360582450692248345, 360582450662736909]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565374676146031, 360565438493440246⟩, ⟨1666345947318853151, 1670577538749686827⟩, true⟩

def words09 : List Nat := [360582450775439686, 360582450888420575, 360582450941320742, 360582450942748315, 360582450939403960, 360582450887852182, 360582450835862660, 360582450776380399, 360582450656431399, 360582450484669877]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981
