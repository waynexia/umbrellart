use std::marker::PhantomData;

use crate::leaf::NodeLeaf;
use crate::node::{Node, NodePtr};

pub struct Art<V> {
    root: NodePtr,
    _phantom: PhantomData<V>,
}

impl<V> Art<V> {
    pub fn new() -> Self {
        Self {
            root: NodePtr::default(),
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&V> {
        if key.is_empty() {
            return None;
        }

        Node::<V>::search(&self.root, key)
            .and_then(|leaf| leaf.cast_to::<NodeLeaf>()?.value.cast_to::<V>())
    }

    pub fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        let leaf = NodeLeaf::new(key.to_vec(), NodePtr::boxed(value));
        Node::<V>::insert(&mut self.root, key, NodePtr::boxed(leaf))
            .and_then(|ptr| ptr.into_option())
            .map(NodePtr::unbox::<V>)
    }

    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        if key.is_empty() {
            return None;
        }

        let leaf = Node::<V>::remove(&mut self.root, key)?.unbox::<NodeLeaf>();
        let item = leaf.value.unbox::<V>();

        Some(item)
    }
}

impl<V> Default for Art<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V> Drop for Art<V> {
    fn drop(&mut self) {
        self.root.drop::<V>();
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_5() {
        let mut art = Art::new();
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
            1,
        );
        art.insert(&[79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0], 2);

        let result = art
            .remove(&[79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0])
            .unwrap();
        assert_eq!(result, 2);
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_6() {
        let mut art = Art::new();
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
                0,
            ],
            1,
        );
        art.insert(&[79, 79, 79, 0], 2);
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
            3,
        );

        let result = art.remove(&[79, 79, 79, 0]).unwrap();
        assert_eq!(result, 2);

        let result = art
            .remove(&[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ])
            .unwrap();
        assert_eq!(result, 3);

        let result = art
            .remove(&[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
                0,
            ])
            .unwrap();
        assert_eq!(result, 1);
    }

    #[test]
    fn fuzz_case_9() {
        let mut art: Art<u64> = Art::new();
        art.insert(&[28, 255, 255, 0], 6909102370521609256);
        art.insert(&[125, 0], 7542684957821053224);
        art.insert(&[4, 0], 10334358167987071613);
        art.insert(&[107, 0], 6827447507943461);
        art.insert(&[63, 234, 180, 0], 6712615244595724288);
        art.insert(&[104, 0], 1125900745703424);
        art.insert(&[141, 0], 18438351909476630016);
        art.insert(&[47, 0], 18377221673217605120);
        art.insert(&[254, 0], 18374967956694744822);
        art.insert(&[226, 95, 0], 280991448656744);
        art.remove(&[]);
        art.insert(&[95, 0], 2821223691570905088);
        art.insert(&[71, 62, 42, 255, 0], 5133825394918610431);
        art.insert(&[186, 0], 18446598368135217405);
        art.insert(&[103, 71, 95, 95, 39, 0], 2821266740687370455);
        art.insert(&[39, 71, 71, 0], 3327365224964500223);
        art.insert(&[61, 191, 0], 2396196477727680000);
        art.insert(&[215, 0], 2738264439729029119);
        art.insert(&[253, 220, 0], 17450349606393646);
        art.insert(&[54, 210, 0], 18446744073692786248);
        art.remove(&[0]);
        art.remove(&[]);
        art.remove(&[]);
        art.insert(&[85, 85, 84, 58, 255, 255, 246, 0], 6124988218704462079);
        art.insert(&[39, 0], 3095498746888447);
        art.remove(&[228, 85, 0]);
        art.insert(&[85, 85, 0], 3819052526439823625);
        art.insert(&[95, 255, 0], 13835058016626803713);
        art.insert(&[37, 0], 6138407387356200961);
        art.remove(&[0]);
        art.insert(&[96, 121, 0], 5860871038790367488);
        art.insert(&[39, 0], 6196715966398857471);
        art.insert(&[26, 39, 0], 3095498880909567);
        art.insert(&[32, 0], 18374686471081688832);
        art.insert(&[71, 70, 123, 0], 67307703805935616);
        art.insert(&[255, 0], 17039783710334320639);
        art.insert(&[121, 121, 0], 2906273114842822912);
        art.insert(&[109, 0], 13336397291522048);
        art.remove(&[]);
        art.remove(&[0]);
        art.insert(
            &[59, 59, 166, 59, 59, 59, 59, 59, 59, 255, 246, 0],
            5425512962855750465,
        );
        art.insert(&[75, 75, 75, 75, 75, 0], 19200);
        art.insert(
            &[75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 0],
            71494644094886626,
        );
        art.insert(
            &[255, 255, 255, 255, 255, 255, 255, 255, 255, 0],
            5425512962855750404,
        );
        art.remove(&[0]);
        art.remove(&[255, 0]);
        art.insert(&[241, 0], 18446744073709487622);
        art.insert(&[181, 181, 1, 0], 2666975404350177280);
        art.insert(&[247, 181, 181, 35, 35, 35, 35, 0], 8753160915110644989);
        art.insert(&[125, 255, 121, 117, 3, 1, 0], 3675781722290550528);
        art.insert(&[61, 128, 0], 0);
        art.insert(&[93, 0], 3602929180896002816);
        art.insert(&[8, 0], 12321848589075611648);
        art.remove(&[0]);
        art.remove(&[121, 0]);
        art.insert(&[152, 0], 562986343226117);
        art.insert(&[121, 255, 121, 0], 8574853694892490101);
        art.insert(&[52, 61, 0], 15914352342448734208);
        art.remove(&[0]);
        art.insert(&[127, 0], 3387541608022749026);
        art.insert(&[85, 85, 247, 0], 288230376134944767);
        art.insert(&[85, 26, 39, 0], 7880573485187327);
        art.insert(&[69, 69, 69, 1, 0], 6568600374109095237);
        art.insert(&[91, 0], 280600864966574079);
        art.insert(&[13, 0], 34359739233);
        art.insert(&[247, 97, 2, 180, 0], 4991396746719741255);
        art.insert(&[255, 98, 0], 949981306899402031);
        art.insert(&[210, 0], 576460766815718703);
        art.insert(&[133, 0], 171418464314062629);
        art.insert(&[2, 13, 0], 17221889707122556783);
        art.insert(&[113, 113, 113, 0], 18374967954638989425);
        art.insert(&[1, 71, 71, 248, 123, 0], 18446744073696837889);
        art.insert(&[71, 71, 0], 17221764975064776704);
        art.remove(&[255, 1, 71, 71, 22, 255, 0]);
        art.insert(&[255, 10, 38, 0], 2667082057182544384);
        art.insert(&[3, 0], 2271221587078285312);
        art.insert(&[31, 31, 0], 6148821965738541055);
        art.insert(&[85, 0], 9583661102699904794);
        art.remove(&[47, 0]);
        art.remove(&[]);
        art.insert(&[255, 0], 18446734178037202687);
        art.insert(&[86, 172, 255, 10, 0], 11601337506997418609);
        art.insert(&[23, 23, 0], 6909102370521609256);
        art.insert(&[125, 0], 7542684957821053224);
        art.insert(&[4, 0], 10334358167987071613);
        art.insert(&[107, 0], 2323846353846309);
        art.insert(&[63, 234, 180, 0], 6712615244595724288);
        art.insert(&[104, 0], 1526726656);
        art.insert(&[143, 0], 4261413119);
        art.remove(&[254, 0]);
        art.insert(&[85, 84, 58, 255, 255, 246, 0], 6124988218704462079);
        art.insert(&[39, 0], 3095498746691839);
        art.remove(&[85, 71, 0]);
        art.insert(&[63, 71, 71, 123, 61, 0], 15437554665361583406);
        art.insert(&[61, 0], 4211239852048712191);
        art.remove(&[0]);
        art.insert(&[85, 0], 2882051936126041856);
        art.insert(&[58, 93, 0], 13744423114240373551);
        art.remove(&[]);
        art.insert(&[0], 18446462770514755584);
    }
}
