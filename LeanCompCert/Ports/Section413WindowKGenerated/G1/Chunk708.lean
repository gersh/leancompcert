import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491917671061707, 362491992128597342⟩, ⟨(-478135552127643797), (-474575353382485941)⟩, true⟩

def state01 : KState := ⟨⟨362472769665083467, 362472844144180805⟩, ⟨877666827461573468, 881228552888757238⟩, true⟩

def words00 : List Nat := [371285289449574289, 371285289452715616, 371285289454678695, 371285289457423817, 371285289459162084, 371285289437891786, 371285289315811512, 371285289249841287, 371285289183031515, 371285289117389233]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481039432066225, 362481113933111387⟩, ⟨292055999753595913, 295619279417177505⟩, true⟩

def words01 : List Nat := [371285288943293511, 371285288896805433, 371285288946796926, 371285288949222828, 371285288783325223, 371285288586030747, 371285288387722901, 371285288333365780, 371285288223739663, 371285288167500221]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473700917035277, 362473775439983697⟩, ⟨811794203812209904, 815359034777682596⟩, true⟩

def words02 : List Nat := [371285288110393261, 371285288037930212, 371285287760054768, 371285287682450977, 371285287603616173, 371285287587815227, 371285287405325018, 371285287224097896, 371285287041922317, 371285286932780220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362459269561227773, 362459344106085898⟩, ⟨1834110881873527197, 1837677264811983097⟩, true⟩

def words03 : List Nat := [371285286794438792, 371285286819642286, 371285286821488079, 371285286805627191, 371285286544103773, 371285286336031292, 371285286126741159, 371285286049840040, 371285285706970792, 371285285343590303]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470433653626074, 362470508220191440⟩, ⟨1043238432011475488, 1046806352798675588⟩, true⟩

def words04 : List Nat := [371285284979046934, 371285284814418473, 371285284549066294, 371285284483561293, 371285284417324170, 371285284319654840, 371285283955908188, 371285283633688580, 371285283310152347, 371285283186356559]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473950779216183, 362474025367847864⟩, ⟨794049057782542873, 797618542082519005⟩, true⟩

def words05 : List Nat := [371285282979651690, 371285282740368992, 371285282500127387, 371285282459797880, 371285282345216163, 371285282265167662, 371285282184289995, 371285282103516106, 371285281783136745, 371285281627261956]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470556128047659, 362470630738339712⟩, ⟨1034599287471402819, 1038170306737146005⟩, true⟩

def words06 : List Nat := [371285281470088022, 371285281378101349, 371285281106718600, 371285280821554775, 371285280535436014, 371285280310848100, 371285280002772908, 371285279894477261, 371285279785341399, 371285279677336991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485246619938787, 362485321252192198⟩, ⟨(-6615925020906117), (-3043349243608785)⟩, true⟩

def words07 : List Nat := [371285279472285406, 371285279447281416, 371285279438187248, 371285279440615288, 371285279194596685, 371285278900011075, 371285278604452084, 371285278508627336, 371285278312786020, 371285278316155128]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475695785463102, 362475770439653833⟩, ⟨670416858380941793, 673990989186784039⟩, true⟩

def words08 : List Nat := [371285278319003470, 371285278321474855, 371285278223294462, 371285278265209448, 371285278366440688, 371285278368873039, 371285278274728971, 371285278181883537, 371285278088072101, 371285278000511314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464504382964284, 362464579058991197⟩, ⟨1463899958244143344, 1467475637129132298⟩, true⟩

def words09 : List Nat := [371285277932541246, 371285277999652321, 371285278065533934, 371285278067962869, 371285277868754824, 371285277678362013, 371285277486632727, 371285277461605557, 371285277171024500, 371285276881799789]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708
