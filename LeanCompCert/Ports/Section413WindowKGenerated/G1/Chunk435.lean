import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk435

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499216891832324, 362499243926404490⟩, ⟨(-597713025254883390), (-596918432351918046)⟩, true⟩

def state01 : KState := ⟨⟨362479171935857781, 362479198983207794⟩, ⟨274339343179051352, 275134491985318684⟩, true⟩

def words00 : List Nat := [371285522695867894, 371285522708877721, 371285522709954265, 371285522655034069, 371285522599573230, 371285522494337882, 371285522235947669, 371285522348485036, 371285522458895321, 371285522460385117]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499948487987643, 362499975548358857⟩, ⟨(-629734714529785298), (-628938999108604464)⟩, true⟩

def words01 : List Nat := [371285522515341884, 371285522716401985, 371285523359999922, 371285523361436372, 371285523301351000, 371285523150738280, 371285523375532427, 371285523490324737, 371285523823395137, 371285524157096970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481201513067051, 362481228586396193⟩, ⟨186194577935069572, 186990857351158326⟩, true⟩

def words02 : List Nat := [371285524457478472, 371285524458915681, 371285524313633881, 371285524469221770, 371285524787033741, 371285524788495461, 371285524668652326, 371285524446904066, 371285524262620425, 371285524264258614]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460078596550956, 362460105682823723⟩, ⟨1105867910544116876, 1106664753463426870⟩, true⟩

def words03 : List Nat := [371285524512630746, 371285524860238539, 371285525110745901, 371285525112183080, 371285524659423371, 371285524366042423, 371285524071920047, 371285524003158657, 371285523461885580, 371285522879733770]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469626102493131, 362469653201617938⟩, ⟨690257577956690032, 691054980519995134⟩, true⟩

def words04 : List Nat := [371285522296956169, 371285522242448428, 371285522201632785, 371285522446102277, 371285522611407530, 371285522612845077, 371285522075193805, 371285521756861863, 371285521437820273, 371285521283834241]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482204176007492, 362482231288260561⟩, ⟨142450583966473562, 143248558329271854⟩, true⟩

def words05 : List Nat := [371285520920563857, 371285520561390157, 371285520282068682, 371285520283684487, 371285520270431466, 371285520336138533, 371285520399569521, 371285520401008943, 371285519896331899, 371285519822657469]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463510250206026, 362463537375275698⟩, ⟨956866051216040343, 957664583937323621⟩, true⟩

def words06 : List Nat := [371285519865627478, 371285519867067774, 371285519419488962, 371285518976328908, 371285518532652314, 371285518247769174, 371285517725848647, 371285517589069620, 371285517451776414, 371285517283100746]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491145828612668, 362491172966658853⟩, ⟨(-247424531317339865), (-246625433142344099)⟩, true⟩

def words07 : List Nat := [371285516779624518, 371285516390336093, 371285516136263362, 371285516137702086, 371285515572847966, 371285514902658192, 371285514231894793, 371285514088581620, 371285513822488170, 371285513953943626]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479702600649833, 362479729751699768⟩, ⟨251359677603513023, 252159342547560981⟩, true⟩

def words08 : List Nat := [371285514114212149, 371285514115685806, 371285514263618496, 371285514538768007, 371285514875374101, 371285514876818177, 371285514800629126, 371285514672555723, 371285514548006783, 371285514549647636]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470210471265176, 362470237635282704⟩, ⟨665270407416299622, 666070637683623628⟩, true⟩

def words09 : List Nat := [371285514811718496, 371285515207074774, 371285515501047965, 371285515502487690, 371285515171862406, 371285514999822052, 371285515179631388, 371285515181071000, 371285514833527732, 371285514484770861]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk435
