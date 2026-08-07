import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk283

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475990449318917, 362476001492517995⟩, ⟨256901403697333540, 257112664688380596⟩, true⟩

def state01 : KState := ⟨⟨362477864441697856, 362477875492990259⟩, ⟨203792879893460765, 204004369966789719⟩, true⟩

def words00 : List Nat := [371285086425291591, 371285086394750660, 371285085820466523, 371285085746866950, 371285085672988665, 371285085186905244, 371285083039207833, 371285082138181401, 371285081580713847, 371285081581650337]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483685861277833, 362483696920804712⟩, ⟨39000391441782174, 39212114674271062⟩, true⟩

def words01 : List Nat := [371285081327793017, 371285081076029873, 371285081456009208, 371285081772925792, 371285082137680520, 371285082502735117, 371285082869511615, 371285082870414925, 371285081577136094, 371285081529373719]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465355953196689, 362465367020777670⟩, ⟨558356444230855026, 558568395597627688⟩, true⟩

def words02 : List Nat := [371285082469864383, 371285082644410358, 371285082821226576, 371285082998319242, 371285083162671450, 371285083163666485, 371285083062680148, 371285083421756802, 371285083518098798, 371285083519033852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507553798548597, 362507564874296299⟩, ⟨(-637294996560547072), (-637082813789671652)⟩, true⟩

def words03 : List Nat := [371285083080002879, 371285083337353699, 371285084507255549, 371285084508159962, 371285084291268761, 371285083879849947, 371285084091603601, 371285084093044830, 371285084886913229, 371285085681120700]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462799515186746, 362462810599105546⟩, ⟨631116592731285300, 631329007112414534⟩, true⟩

def words04 : List Nat := [371285086349170449, 371285086350074976, 371285085593644967, 371285085357074186, 371285085257539088, 371285085258443242, 371285083740276259, 371285081979460768, 371285080218409195, 371285079699885526]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362438836430565841, 362438847522630178⟩, ⟨1310759569107558795, 1310972214456750283⟩, true⟩

def words05 : List Nat := [371285079371468486, 371285079828876965, 371285080268965184, 371285080269869530, 371285079054309003, 371285078120829196, 371285077186966070, 371285076772742082, 371285075252290347, 371285073623280981]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470861713233751, 362470872813400406⟩, ⟨402531020532744271, 402743895705125625⟩, true⟩

def words06 : List Nat := [371285071993977657, 371285071452433451, 371285070535871553, 371285070640888891, 371285070641590185, 371285070573688970, 371285069324808043, 371285068983716453, 371285068931452433, 371285068932388955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462222354056300, 362462233462467370⟩, ⟨647711294546488322, 647924403654845734⟩, true⟩

def words07 : List Nat := [371285068432703852, 371285067723573647, 371285067096710521, 371285067097707475, 371285066559127821, 371285066320172502, 371285066080928610, 371285065847942674, 371285064583082619, 371285063779720889]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462210109487660, 362462221225956785⟩, ⟨648087154435945045, 648300492273780785⟩, true⟩

def words08 : List Nat := [371285063219798041, 371285063220704920, 371285062137572608, 371285061057303570, 371285059976763378, 371285058946204849, 371285057466998541, 371285057226846473, 371285056986414501, 371285056748756144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482728583917268, 362482739708595539⟩, ⟨65458147950997440, 65671718886552118⟩, true⟩

def words09 : List Nat := [371285055945053533, 371285055477550413, 371285055779148974, 371285055780054969, 371285054899564379, 371285053824867909, 371285052771402898, 371285052772400884, 371285052173457848, 371285052093063376]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk283
