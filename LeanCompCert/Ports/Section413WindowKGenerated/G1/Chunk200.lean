import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk200

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504014679867108, 362504020035284987⟩, ⟨(-382817072544680820), (-382744632229059980)⟩, true⟩

def state01 : KState := ⟨⟨362462613435775846, 362462618796786589⟩, ⟨445361181596995630, 445433733798492790⟩, true⟩

def words00 : List Nat := [371284884581120434, 371284884581740901, 371284882666012437, 371284882805085405, 371284883709590457, 371284883710221634, 371284882537575340, 371284881306455445, 371284880075205338, 371284879353198308]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362422153715035100, 362422159081640787⟩, ⟨1255397248719877407, 1255469912904342269⟩, true⟩

def words01 : List Nat := [371284879617880111, 371284880995086334, 371284881842430533, 371284881843051514, 371284879369200512, 371284877661061028, 371284876134745553, 371284876135366605, 371284872998353543, 371284869866501144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498343931419769, 362498349303574518⟩, ⟨(-270122520133680147), (-270049744827956025)⟩, true⟩

def words02 : List Nat := [371284866734672651, 371284866089358403, 371284865285755363, 371284866127205872, 371284866514219048, 371284866514843962, 371284865232640683, 371284865007126673, 371284867039085682, 371284867712798823]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484567419777102, 362484572797601174⟩, ⟨5890292648542193, 5963181539243933⟩, true⟩

def words03 : List Nat := [371284867875977776, 371284868039355496, 371284869093086275, 371284869309375742, 371284870289360136, 371284871269478552, 371284872254031589, 371284872254653752, 371284870375625116, 371284870361550239]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362457209678734763, 362457215062107793⟩, ⟨554307207722227741, 554380207842972547⟩, true⟩

def words04 : List Nat := [371284871291749996, 371284871292376111, 371284870022334614, 371284868441733680, 371284866861059541, 371284865799968689, 371284864292633779, 371284864779523432, 371284864947141175, 371284864947785747]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362514653366250589, 362514658755237654⟩, ⟨(-597671496093265141), (-597598383382527629)⟩, true⟩

def words05 : List Nat := [371284864669875320, 371284865771153933, 371284868144243660, 371284868144866361, 371284867710839770, 371284866736634163, 371284866861744246, 371284866862429682, 371284868207016319, 371284869692709240]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481551934164337, 362481557328781300⟩, ⟨66552486383737826, 66625712058126292⟩, true⟩

def words06 : List Nat := [371284871191607654, 371284871192241089, 371284872535188582, 371284874445230808, 371284877117666539, 371284877118289488, 371284876920187199, 371284876727646973, 371284876994834390, 371284876995550515]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362425233646607237, 362425239046838362⟩, ⟨1197439898193887229, 1197513236573438203⟩, true⟩

def words07 : List Nat := [371284879139815057, 371284881449506846, 371284883764176744, 371284883764799809, 371284882778084728, 371284881909613307, 371284881734583089, 371284881735206310, 371284879129629649, 371284876160213534]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478200982291685, 362478206388109064⟩, ⟨133559270974542688, 133632721554265426⟩, true⟩

def words08 : List Nat := [371284873190809037, 371284872276016280, 371284870122228100, 371284868513230999, 371284866904208370, 371284865037056601, 371284861125982713, 371284859291329343, 371284858090864784, 371284858091521422]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488086487052881, 362488091898541380⟩, ⟨(-65031562156072355), (-64957997614726065)⟩, true⟩

def words09 : List Nat := [371284857760909208, 371284857211242692, 371284858258663139, 371284858866418384, 371284860237840807, 371284861609373682, 371284861974567439, 371284861975194179, 371284860156601315, 371284860318141663]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk200
