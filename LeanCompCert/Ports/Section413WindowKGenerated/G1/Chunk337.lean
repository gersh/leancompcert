import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk337

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469955851172709, 362469971741099921⟩, ⟨493371946386427275, 493733866311362997⟩, true⟩

def state01 : KState := ⟨⟨362496881138650610, 362496897038326206⟩, ⟨(-414023331862420774), (-413661083366753172)⟩, true⟩

def words00 : List Nat := [371284622472537168, 371284622473738611, 371284623190196072, 371284623989279449, 371284624570752399, 371284624571845267, 371284624594023112, 371284624943874613, 371284625868898218, 371284626234037792]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490135657026309, 362490151566658237⟩, ⟨(-186521446919294676), (-186158862745087308)⟩, true⟩

def words01 : List Nat := [371284626507007845, 371284626780362521, 371284627932891250, 371284628645920574, 371284629388561988, 371284630131561176, 371284630872463171, 371284630873555623, 371284630839831753, 371284631004909028]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493590629300189, 362493606548658117⟩, ⟨(-302949167794562568), (-302586255609855954)⟩, true⟩

def words02 : List Nat := [371284632048649275, 371284632258049950, 371284632463705437, 371284632669698134, 371284633054305730, 371284633229973586, 371284634057996146, 371284634886431366, 371284635712793649, 371284635979875400]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362520277446385931, 362520293375605229⟩, ⟨(-1203248284767251535), (-1202885039907311007)⟩, true⟩

def words03 : List Nat := [371284637005015339, 371284638030658361, 371284639335594586, 371284639584347982, 371284639751593929, 371284639919174778, 371284640535754475, 371284640715282214, 371284641772711758, 371284642830573745]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484576458804078, 362484592397887887⟩, ⟨1357510486996567, 1721088223811953⟩, true⟩

def words04 : List Nat := [371284643786963075, 371284643788054981, 371284644015310560, 371284644457725272, 371284644965105943, 371284644966198325, 371284644478020367, 371284643823822343, 371284643391835581, 371284643393094519]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481761882153695, 362481777831072056⟩, ⟨96533130916544612, 96897040620514018⟩, true⟩

def words05 : List Nat := [371284644268690696, 371284645146198692, 371284646021674730, 371284646170561032, 371284646502968670, 371284646835884083, 371284648045875908, 371284648087022713, 371284648087853538, 371284648004076219]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500327237817126, 362500343196533211⟩, ⟨(-530380811200673321), (-530016570676282235)⟩, true⟩

def words06 : List Nat := [371284647995805833, 371284647997012290, 371284648060693003, 371284648415396194, 371284648625658611, 371284648626751369, 371284647668338569, 371284647587663163, 371284648301385846, 371284648767269160]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499814963869974, 362499830932516373⟩, ⟨(-512986751626877780), (-512622175703729468)⟩, true⟩

def words07 : List Nat := [371284649231264336, 371284649695590462, 371284651036253728, 371284652047542062, 371284653116238152, 371284654185288587, 371284655259017239, 371284655260110377, 371284655615139952, 371284656065706518]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473633374344399, 362473649352739904⟩, ⟨371628396569009513, 371993301867712797⟩, true⟩

def words08 : List Nat := [371284656800097210, 371284657000823231, 371284657199964770, 371284657399473195, 371284657741484481, 371284657742699876, 371284657928725593, 371284658211126219, 371284658327690784, 371284658328823589]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362532029572918523, 362532045561217343⟩, ⟨(-1601864587628648529), (-1601499347649485937)⟩, true⟩

def words09 : List Nat := [371284658553874007, 371284659105277844, 371284660386681219, 371284660649342409, 371284660774819694, 371284660900635559, 371284661901591096, 371284662519859495, 371284663922467456, 371284665325495043]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk337
