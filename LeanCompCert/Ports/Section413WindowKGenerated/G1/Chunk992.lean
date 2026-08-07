import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492249408125888, 362492399436613125⟩, ⟨(-708604925482008921), (-698556909980835455)⟩, true⟩

def state01 : KState := ⟨⟨362475719896013741, 362475869955916694⟩, ⟨931189786481951646, 941240918587867044⟩, true⟩

def words00 : List Nat := [371285357673531694, 371285357677018256, 371285357625193439, 371285357634184748, 371285357672008872, 371285357675495506, 371285357578056721, 371285357480202856, 371285357380917874, 371285357315241237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472717023011421, 362472867114345540⟩, ⟨1229123613261224319, 1239177863807865627⟩, true⟩

def words01 : List Nat := [371285357222018444, 371285357172116313, 371285357121057881, 371285357070765945, 371285356896465085, 371285356754606076, 371285356610832460, 371285356553825213, 371285356430660827, 371285356308699581]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478502066146973, 362478652188634534⟩, ⟨655156636248466898, 665213977999941602⟩, true⟩

def words02 : List Nat := [371285356185191248, 371285356158424134, 371285356117348662, 371285356150256827, 371285356156988742, 371285356160476130, 371285356031408394, 371285355989905494, 371285355946649318, 371285355947356695]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477220891215802, 362477371045543806⟩, ⟨782311336446739290, 792371837884107586⟩, true⟩

def words03 : List Nat := [371285355882425820, 371285355795737393, 371285355718529953, 371285355722412087, 371285355688678420, 371285355674251662, 371285355658683627, 371285355641479346, 371285355521463271, 371285355445361260]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481675158769475, 362481825344171658⟩, ⟨340283340711113206, 350346926111432746⟩, true⟩

def words04 : List Nat := [371285355388407738, 371285355391936342, 371285355353590426, 371285355316327947, 371285355277762804, 371285355253393193, 371285355223159147, 371285355254445221, 371285355284395601, 371285355288011572]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493957894471110, 362494108111398725⟩, ⟨(-878859742122490886), (-868793027661283950)⟩, true⟩

def words05 : List Nat := [371285355320814508, 371285355390997229, 371285355470945846, 371285355474434316, 371285355419356919, 371285355356202193, 371285355326168428, 371285355330013921, 371285355407185112, 371285355499318842]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480677994924346, 362480828243363622⟩, ⟨439338882880158977, 449408725343990449⟩, true⟩

def words06 : List Nat := [371285355580530909, 371285355584022500, 371285355579023995, 371285355611631144, 371285355672994989, 371285355676483938, 371285355602772639, 371285355499470019, 371285355394756628, 371285355378705055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477024318472415, 362477174598337021⟩, ⟨802097548119846522, 812170510337186848⟩, true⟩

def words07 : List Nat := [371285355368466355, 371285355405282009, 371285355440799319, 371285355444350579, 371285355396301768, 371285355351818537, 371285355358452645, 371285355361941948, 371285355282220431, 371285355203799725]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484520649164410, 362484670960295294⟩, ⟨57817619058004611, 67893685553014781⟩, true⟩

def words08 : List Nat := [371285355123819898, 371285355070896318, 371285354965807737, 371285354948507408, 371285354930151725, 371285354896961515, 371285354771697353, 371285354732214254, 371285354748459582, 371285354752072442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483412356330418, 362483562699210491⟩, ⟨167880429377287271, 177959648406214077⟩, true⟩

def words09 : List Nat := [371285354747797358, 371285354735890138, 371285354791237999, 371285354838387438, 371285354890347319, 371285354943654413, 371285354959775552, 371285354963265899, 371285354854442053, 371285354840684874]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk992
