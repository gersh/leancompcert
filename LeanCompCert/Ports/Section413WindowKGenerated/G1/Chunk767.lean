import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492364883391329, 362492452812470626⟩, ⟨(-560295725532993609), (-555741430549010323)⟩, true⟩

def state01 : KState := ⟨⟨362475485021381242, 362475572974302945⟩, ⟨734405314375481170, 738961438192672374⟩, true⟩

def words00 : List Nat := [371285207338630553, 371285207341274166, 371285207197343084, 371285207107982500, 371285207017272864, 371285206929798419, 371285206700240187, 371285206468835232, 371285206236384166, 371285206156915286]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471383539027122, 362471471515813326⟩, ⟨1049096862164042452, 1053654816747093458⟩, true⟩

def words01 : List Nat := [371285206036880583, 371285206043523587, 371285206045543842, 371285206027755841, 371285205860717157, 371285205728408501, 371285205629006367, 371285205631650750, 371285205461538270, 371285205285583231]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479535058545725, 362479623058979205⟩, ⟨423707261640100479, 428267030562381137⟩, true⟩

def words02 : List Nat := [371285205108372175, 371285205039952457, 371285204922940983, 371285204943095630, 371285204945179068, 371285204927899352, 371285204753044239, 371285204627966948, 371285204537155972, 371285204539893612]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489306611344338, 362489394635856992⟩, ⟨(-326095149452866809), (-321533532816549983)⟩, true⟩

def words03 : List Nat := [371285204469129286, 371285204399315490, 371285204425467756, 371285204475918260, 371285204558187609, 371285204641525767, 371285204723996941, 371285204726650805, 371285204724703226, 371285204782547594]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471277091075797, 362471365139145329⟩, ⟨1057572581530836448, 1062136006046673482⟩, true⟩

def words04 : List Nat := [371285204881202275, 371285204883847257, 371285204756461857, 371285204628932820, 371285204500369403, 371285204424760152, 371285204263163817, 371285204190688638, 371285204117296169, 371285204044761573]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488027721973164, 362488115793992485⟩, ⟨(-228143982525329782), (-223578719748238166)⟩, true⟩

def words05 : List Nat := [371285203866249821, 371285203774851301, 371285203756937960, 371285203759583208, 371285203610475552, 371285203402012420, 371285203192499761, 371285203153697579, 371285203092712176, 371285203133660439]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471562176269847, 362471650272195899⟩, ⟨1035846439133911323, 1040413537116663421⟩, true⟩

def words06 : List Nat := [371285203175491099, 371285203178182923, 371285203102792180, 371285203130066058, 371285203187632757, 371285203190278766, 371285203042139764, 371285202895031856, 371285202746857253, 371285202617345263]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472163958753992, 362472252078487090⟩, ⟨989691196967927362, 994260122739635678⟩, true⟩

def words07 : List Nat := [371285202442610303, 371285202438446125, 371285202433404562, 371285202416450560, 371285202216272551, 371285202046900727, 371285201876082411, 371285201875622191, 371285201711783312, 371285201546092452]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479069922861832, 362479158066289146⟩, ⟨459450546323831023, 464021291459426275⟩, true⟩

def words08 : List Nat := [371285201380061234, 371285201382977787, 371285201311378945, 371285201310403849, 371285201308569630, 371285201280146409, 371285201024916680, 371285200913678926, 371285200801072718, 371285200797002253]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482567256911424, 362482655424468645⟩, ⟨190867722636243320, 195440320822405124⟩, true⟩

def words09 : List Nat := [371285200720312913, 371285200617632772, 371285200537497078, 371285200540413677, 371285200481135993, 371285200474675510, 371285200467401581, 371285200425298183, 371285200250124504, 371285200220312687]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767
