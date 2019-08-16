J$.iids = {"nBranches":8,"originalCodeFileName":"/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/symbolicArrayIndex.js","instrumentedCodeFileName":"/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/symbolicArrayIndex_jalangi_.js"};
jalangiLabel241:
    while (true) {
        try {
            J$.Se(529, '/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/symbolicArrayIndex_jalangi_.js', '/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/symbolicArrayIndex.js');
            function getItem(base, offset) {
                jalangiLabel240:
                    while (true) {
                        try {
                            J$.Fe(337, arguments.callee, this, arguments);
                            arguments = J$.N(345, 'arguments', arguments, 4);
                            base = J$.N(353, 'base', base, 4);
                            offset = J$.N(361, 'offset', offset, 4);
                            J$.N(369, 'ret', ret, 0);
                            J$.N(377, 'j', j, 0);
                            var ret;
                            for (var j = J$.X1(193, J$.W(185, 'j', J$.T(177, 0, 22, false), j, 1)); J$.X1(585, J$.C(16, J$.B(10, '<', J$.R(201, 'j', j, 0), J$.G(217, J$.R(209, 'base', base, 0), 'length', 0), 0))); J$.X1(593, J$.B(34, '-', j = J$.W(241, 'j', J$.B(26, '+', J$.U(18, '+', J$.R(233, 'j', j, 0)), J$.T(225, 1, 22, false), 0), j, 0), J$.T(249, 1, 22, false), 0))) {
                                if (J$.X1(577, J$.C(8, J$.B(42, '===', J$.R(257, 'j', j, 0), J$.R(265, 'offset', offset, 0), 0)))) {
                                    J$.X1(305, ret = J$.W(297, 'ret', J$.G(289, J$.R(273, 'base', base, 0), J$.R(281, 'j', j, 0), 4), ret, 0));
                                }
                            }
                            return J$.X1(329, J$.Rt(321, J$.R(313, 'ret', ret, 0)));
                        } catch (J$e) {
                            J$.Ex(601, J$e);
                        } finally {
                            if (J$.Fr(609))
                                continue jalangiLabel240;
                            else
                                return J$.Ra();
                        }
                    }
            }
            J$.N(537, 'a', a, 0);
            J$.N(545, 'i', i, 0);
            J$.N(553, 'j', j, 0);
            getItem = J$.N(569, 'getItem', J$.T(561, getItem, 12, false, 337), 0);
            var a = J$.X1(105, J$.W(97, 'a', J$.T(89, [
                J$.T(9, 3, 22, false),
                J$.T(17, 5, 22, false),
                J$.T(25, "r", 21, false),
                J$.T(33, 9, 22, false),
                J$.T(41, "j", 21, false),
                J$.T(49, 3, 22, false),
                J$.T(57, 2, 22, false),
                J$.T(65, 1, 22, false),
                J$.T(73, 8, 22, false),
                J$.T(81, "Hello", 21, false)
            ], 10, false), a, 3));
            var i = J$.X1(137, J$.W(129, 'i', J$.M(121, J$, 'readInput', 0)(J$.T(113, 0, 22, false)), i, 3));
            var j = J$.X1(169, J$.W(161, 'j', J$.M(153, J$, 'readInput', 0)(J$.T(145, 0, 22, false)), j, 3));
            if (J$.X1(617, J$.C(24, J$.B(50, '===', J$.F(409, J$.R(385, 'getItem', getItem, 1), 0)(J$.R(393, 'a', a, 1), J$.R(401, 'i', i, 1)), J$.T(417, 3, 22, false), 0)))) {
                J$.X1(449, J$.M(441, J$.R(425, 'console', console, 2), 'log', 0)(J$.T(433, "1", 21, false)));
            }
            if (J$.X1(625, J$.C(32, J$.B(58, '===', J$.F(481, J$.R(457, 'getItem', getItem, 1), 0)(J$.R(465, 'a', a, 1), J$.R(473, 'j', j, 1)), J$.T(489, 8, 22, false), 0)))) {
                J$.X1(521, J$.M(513, J$.R(497, 'console', console, 2), 'log', 0)(J$.T(505, "2", 21, false)));
            }
        } catch (J$e) {
            J$.Ex(633, J$e);
        } finally {
            if (J$.Sr(641)) {
                J$.L();
                continue jalangiLabel241;
            } else {
                J$.L();
                break jalangiLabel241;
            }
        }
    }
// JALANGI DO NOT INSTRUMENT
