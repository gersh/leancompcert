import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489301474269960, 362489434446407019⟩, ⟨(-408996737053729349), (-400593448843328903)⟩, true⟩

def state01 : KState := ⟨⟨362492901750823250, 362493034752117775⟩, ⟨(-745996910369434069), (-737590892866827671)⟩, true⟩

def words00 : List Nat := [371285154809730475, 371285154856095047, 371285154892154798, 371285154929351893, 371285154989349870, 371285154993783830, 371285155111015907, 371285155229609225, 371285155345930268, 371285155433524161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498102169559172, 362498235200467598⟩, ⟨(-1232863783989357088), (-1224454994179881588)⟩, true⟩

def words01 : List Nat := [371285155553524377, 371285155675150667, 371285155848097146, 371285155869957349, 371285155876014656, 371285155883135748, 371285155993877125, 371285156065411208, 371285156207343529, 371285156350699065]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489331820728088, 362489464881152871⟩, ⟨(-411790909342376407), (-403379356059686735)⟩, true⟩

def words02 : List Nat := [371285156472655133, 371285156475932378, 371285156517127514, 371285156592659322, 371285156670492052, 371285156673785160, 371285156646710514, 371285156611289710, 371285156649750820, 371285156699502994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480705502917594, 362480838592952076⟩, ⟨395981771050119320, 404396096829956132⟩, true⟩

def words03 : List Nat := [371285156852643952, 371285157007259364, 371285157145744639, 371285157149022146, 371285157144671570, 371285157157983098, 371285157283690960, 371285157286968553, 371285157260912816, 371285157218505579]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488838747981761, 362488971867325369⟩, ⟨(-365643266546996344), (-357226196106459924)⟩, true⟩

def words04 : List Nat := [371285157212822422, 371285157216434786, 371285157239317044, 371285157282107683, 371285157304658590, 371285157307993610, 371285157249157574, 371285157266895076, 371285157382389091, 371285157426517407]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485711580252399, 362485844729477845⟩, ⟨(-72766686369691188), (-64346817346021132)⟩, true⟩

def words05 : List Nat := [371285157469339967, 371285157513248946, 371285157575462395, 371285157601786696, 371285157661437132, 371285157722377462, 371285157781874334, 371285157785152466, 371285157699786345, 371285157711216819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477129113528710, 362477262291931274⟩, ⟨731112712860356931, 739535314765505015⟩, true⟩

def words06 : List Nat := [371285157821970463, 371285157825248855, 371285157784298816, 371285157743407397, 371285157701240637, 371285157656272992, 371285157557547588, 371285157507449788, 371285157456274569, 371285157405785929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498972164819856, 362499105372899352⟩, ⟨(-1315029609719752800), (-1306604227824780560)⟩, true⟩

def words07 : List Nat := [371285157334876944, 371285157350020628, 371285157469283431, 371285157494879240, 371285157501359133, 371285157508852119, 371285157621495232, 371285157692141442, 371285157843254249, 371285157995866392]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485194616545241, 362485327854256549⟩, ⟨(-24303314255205835), (-15875156303501403)⟩, true⟩

def words08 : List Nat := [371285158123700079, 371285158126982003, 371285158236114285, 371285158350443326, 371285158481411408, 371285158484691118, 371285158473484772, 371285158425289007, 371285158407031554, 371285158412620709]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478080646544505, 362478213913731459⟩, ⟨642267594911493276, 650698514586417800⟩, true⟩

def words09 : List Nat := [371285158492064853, 371285158572803638, 371285158652208327, 371285158655488552, 371285158597115678, 371285158545301526, 371285158529942720, 371285158533245059, 371285158472070050, 371285158401613919]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936
