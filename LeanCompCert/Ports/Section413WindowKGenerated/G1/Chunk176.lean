import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk176

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362558255293804976, 362558259394517477⟩, ⟨(-1277913859258345745), (-1277865042084148371)⟩, true⟩

def state01 : KState := ⟨⟨362515652389759582, 362515656495340830⟩, ⟨(-528048464678891164), (-527999561789540468)⟩, true⟩

def words00 : List Nat := [371285661673594607, 371285662747414231, 371285666159548392, 371285669571573614, 371285673159720410, 371285673160261263, 371285672454386709, 371285671747191238, 371285673555384221, 371285675258512170]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362452672018952643, 362452676129407433⟩, ⟨581517923420068520, 581566912157730622⟩, true⟩

def words01 : List Nat := [371285678611859139, 371285681965048951, 371285685165583550, 371285685166124735, 371285684076698944, 371285683596890307, 371285685303576143, 371285685304118193, 371285684069786948, 371285682197066783]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362538006040205142, 362538010155504789⟩, ⟨(-922296126234587940), (-922247052105872536)⟩, true⟩

def words02 : List Nat := [371285681078021516, 371285681078626881, 371285683610972281, 371285686486101429, 371285688830782030, 371285688831332805, 371285691430195991, 371285694338189610, 371285698921131915, 371285701888695994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501144082440574, 362501148202690608⟩, ⟨(-272209181162729906), (-272160019734423644)⟩, true⟩

def words03 : List Nat := [371285704878987171, 371285707869126621, 371285711100881745, 371285712724971625, 371285715302952475, 371285717880842856, 371285720456732859, 371285720457274846, 371285719629451100, 371285720504729358]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362421791260196233, 362421795385271281⟩, ⟨1127995660811637591, 1128044907378642609⟩, true⟩

def words04 : List Nat := [371285722451167477, 371285722451709562, 371285720121853614, 371285717792395267, 371285715462995270, 371285714089993006, 371285711479536371, 371285710183500049, 371285708887425290, 371285707278040610]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362549024436811087, 362549028566779954⟩, ⟨(-1118338902811495014), (-1118289569843320956)⟩, true⟩

def words05 : List Nat := [371285703657544525, 371285702339194235, 371285702468267764, 371285702468822166, 371285702104248192, 371285700765556095, 371285701291098314, 371285701674712804, 371285705260975641, 371285708847067406]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362511135053283736, 362511139188156907⟩, ⟨(-449366176990545778), (-449316757387872230)⟩, true⟩

def words06 : List Nat := [371285711596732418, 371285711597275173, 371285710584032794, 371285711087793395, 371285712550066440, 371285712550612945, 371285711430815369, 371285710208189221, 371285710961312368, 371285712400912956]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362426066259659212, 362426070399424601⟩, ⟨1054485198847697196, 1054534704920659264⟩, true⟩

def words07 : List Nat := [371285716211668977, 371285720022218416, 371285723661045246, 371285723661588497, 371285723040310040, 371285722371954019, 371285722680403683, 371285722680946985, 371285719400722277, 371285716027530974]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474701251199540, 362474705395832283⟩, ⟨194703013562687518, 194752605715137490⟩, true⟩

def words08 : List Nat := [371285712654469392, 371285712476329023, 371285713025666134, 371285714897488474, 371285716210561997, 371285716211105861, 371285713894827651, 371285713830910211, 371285714587225977, 371285714587789047]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362445935380808647, 362445939530388009⟩, ⟨703886924933336435, 703936604616799625⟩, true⟩

def words09 : List Nat := [371285713965890980, 371285713347818869, 371285714178541755, 371285714179145750, 371285714902832771, 371285715744692466, 371285716099266551, 371285716099810479, 371285712206404478, 371285709960027377]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk176
