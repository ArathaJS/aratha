J$.iids = {"nBranches":26,"originalCodeFileName":"/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/Bresenham-drawline.js","instrumentedCodeFileName":"/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/Bresenham-drawline_jalangi_.js"};
jalangiLabel85:
    while (true) {
        try {
            J$.Se(1065, '/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/Bresenham-drawline_jalangi_.js', '/home/roberto/jalangi2-concolic/experiments/test/benchmarks/jalangi/Bresenham-drawline.js');
            function calc_abs(a) {
                jalangiLabel82:
                    while (true) {
                        try {
                            J$.Fe(81, arguments.callee, this, arguments);
                            arguments = J$.N(89, 'arguments', arguments, 4);
                            a = J$.N(97, 'a', a, 4);
                            if (J$.X1(1137, J$.C(8, J$.B(10, '<', J$.R(9, 'a', a, 0), J$.T(17, 0, 22, false), 0)))) {
                                return J$.X1(49, J$.Rt(41, J$.B(18, '-', J$.T(25, 0, 22, false), J$.R(33, 'a', a, 0), 0)));
                            } else {
                                return J$.X1(73, J$.Rt(65, J$.R(57, 'a', a, 0)));
                            }
                        } catch (J$e) {
                            J$.Ex(1145, J$e);
                        } finally {
                            if (J$.Fr(1153))
                                continue jalangiLabel82;
                            else
                                return J$.Ra();
                        }
                    }
            }
            function drawLine(x1, y1, x2, y2) {
                jalangiLabel83:
                    while (true) {
                        try {
                            J$.Fe(625, arguments.callee, this, arguments);
                            arguments = J$.N(633, 'arguments', arguments, 4);
                            x1 = J$.N(641, 'x1', x1, 4);
                            y1 = J$.N(649, 'y1', y1, 4);
                            x2 = J$.N(657, 'x2', x2, 4);
                            y2 = J$.N(665, 'y2', y2, 4);
                            J$.N(673, 'dx', dx, 0);
                            J$.N(681, 'dy', dy, 0);
                            J$.N(689, 'error', error, 0);
                            J$.N(697, 'doubledError', doubledError, 0);
                            J$.N(705, 'cx', cx, 0);
                            J$.N(713, 'cy', cy, 0);
                            var dx = J$.X1(193, J$.W(185, 'dx', J$.F(129, J$.R(105, 'calc_abs', calc_abs, 1), 0)(J$.B(26, '-', J$.R(113, 'x2', x2, 0), J$.R(121, 'x1', x1, 0), 0)), dx, 1)), dy = J$.X1(209, J$.W(201, 'dy', J$.F(161, J$.R(137, 'calc_abs', calc_abs, 1), 0)(J$.B(34, '-', J$.R(145, 'y2', y2, 0), J$.R(153, 'y1', y1, 0), 0)), dy, 1)), error = J$.X1(225, J$.W(217, 'error', J$.B(42, '-', J$.R(169, 'dx', dx, 0), J$.R(177, 'dy', dy, 0), 0), error, 1)), doubledError;
                            var cx, cy;
                            if (J$.X1(1161, J$.C(16, J$.B(50, '<', J$.R(233, 'x1', x1, 0), J$.R(241, 'x2', x2, 0), 0)))) {
                                J$.X1(265, cx = J$.W(257, 'cx', J$.T(249, 1, 22, false), cx, 0));
                            } else {
                                J$.X1(289, cx = J$.W(281, 'cx', J$.U(58, '-', J$.T(273, 1, 22, false)), cx, 0));
                            }
                            if (J$.X1(1169, J$.C(24, J$.B(66, '<', J$.R(297, 'y1', y1, 0), J$.R(305, 'y2', y2, 0), 0)))) {
                                J$.X1(329, cy = J$.W(321, 'cy', J$.T(313, 1, 22, false), cy, 0));
                            } else {
                                J$.X1(353, cy = J$.W(345, 'cy', J$.U(74, '-', J$.T(337, 1, 22, false)), cy, 0));
                            }
                            while (J$.X1(1193, J$.C(56, J$.C(32, J$.B(82, '!==', J$.R(361, 'x1', x1, 0), J$.R(369, 'x2', x2, 0), 0)) ? J$._() : J$.B(90, '!==', J$.R(377, 'y1', y1, 0), J$.R(385, 'y2', y2, 0), 0)))) {
                                J$.X1(425, J$.F(417, J$.R(393, 'drawPoint', drawPoint, 1), 0)(J$.R(401, 'x1', x1, 0), J$.R(409, 'y1', y1, 0)));
                                J$.X1(457, doubledError = J$.W(449, 'doubledError', J$.B(98, '+', J$.R(433, 'error', error, 0), J$.R(441, 'error', error, 0), 0), doubledError, 0));
                                if (J$.X1(1177, J$.C(40, J$.B(114, '>', J$.R(465, 'doubledError', doubledError, 0), J$.U(106, '-', J$.R(473, 'dy', dy, 0)), 0)))) {
                                    J$.X1(505, error = J$.W(497, 'error', J$.B(122, '-', J$.R(489, 'error', error, 0), J$.R(481, 'dy', dy, 0), 0), error, 0));
                                    J$.X1(537, x1 = J$.W(529, 'x1', J$.B(130, '+', J$.R(521, 'x1', x1, 0), J$.R(513, 'cx', cx, 0), 0), x1, 0));
                                }
                                if (J$.X1(1185, J$.C(48, J$.B(138, '<', J$.R(545, 'doubledError', doubledError, 0), J$.R(553, 'dx', dx, 0), 0)))) {
                                    J$.X1(585, error = J$.W(577, 'error', J$.B(146, '+', J$.R(569, 'error', error, 0), J$.R(561, 'dx', dx, 0), 0), error, 0));
                                    J$.X1(617, y1 = J$.W(609, 'y1', J$.B(154, '+', J$.R(601, 'y1', y1, 0), J$.R(593, 'cy', cy, 0), 0), y1, 0));
                                }
                            }
                        } catch (J$e) {
                            J$.Ex(1201, J$e);
                        } finally {
                            if (J$.Fr(1209))
                                continue jalangiLabel83;
                            else
                                return J$.Ra();
                        }
                    }
            }
            function drawPoint(x, y) {
                jalangiLabel84:
                    while (true) {
                        try {
                            J$.Fe(721, arguments.callee, this, arguments);
                            arguments = J$.N(729, 'arguments', arguments, 4);
                            x = J$.N(737, 'x', x, 4);
                            y = J$.N(745, 'y', y, 4);
                        } catch (J$e) {
                            J$.Ex(1217, J$e);
                        } finally {
                            if (J$.Fr(1225))
                                continue jalangiLabel84;
                            else
                                return J$.Ra();
                        }
                    }
            }
            calc_abs = J$.N(1081, 'calc_abs', J$.T(1073, calc_abs, 12, false, 81), 0);
            drawLine = J$.N(1097, 'drawLine', J$.T(1089, drawLine, 12, false, 625), 0);
            drawPoint = J$.N(1113, 'drawPoint', J$.T(1105, drawPoint, 12, false, 721), 0);
            J$.N(1121, 'x1', x1, 0);
            J$.N(1129, 'y1', y1, 0);
            var x1 = J$.X1(777, J$.W(769, 'x1', J$.M(761, J$, 'readInput', 0)(J$.T(753, 1, 22, false)), x1, 3));
            var y1 = J$.X1(809, J$.W(801, 'y1', J$.M(793, J$, 'readInput', 0)(J$.T(785, 2, 22, false)), y1, 3));
            if (J$.X1(1265, J$.C(104, J$.C(64, J$.B(170, '===', J$.U(162, 'typeof', J$.R(817, 'x1', x1, 1)), J$.T(825, "number", 21, false), 0)) ? J$.B(186, '===', J$.U(178, 'typeof', J$.R(833, 'y1', y1, 1)), J$.T(841, "number", 21, false), 0) : J$._()))) {
                if (J$.X1(1233, J$.C(72, J$.B(194, '>', J$.R(849, 'x1', x1, 1), J$.T(857, 4, 22, false), 0)))) {
                    J$.X1(881, x1 = J$.W(873, 'x1', J$.T(865, 3, 22, false), x1, 2));
                }
                if (J$.X1(1241, J$.C(80, J$.B(210, '<', J$.R(889, 'x1', x1, 1), J$.U(202, '-', J$.T(897, 4, 22, false)), 0)))) {
                    J$.X1(921, x1 = J$.W(913, 'x1', J$.U(218, '-', J$.T(905, 3, 22, false)), x1, 2));
                }
                if (J$.X1(1249, J$.C(88, J$.B(226, '>', J$.R(929, 'y1', y1, 1), J$.T(937, 4, 22, false), 0)))) {
                    J$.X1(961, y1 = J$.W(953, 'y1', J$.T(945, 4, 22, false), y1, 2));
                }
                if (J$.X1(1257, J$.C(96, J$.B(242, '<', J$.R(969, 'y1', y1, 1), J$.U(234, '-', J$.T(977, 4, 22, false)), 0)))) {
                    J$.X1(1001, y1 = J$.W(993, 'y1', J$.U(250, '-', J$.T(985, 4, 22, false)), y1, 2));
                }
                J$.X1(1057, J$.F(1049, J$.R(1009, 'drawLine', drawLine, 1), 0)(J$.R(1017, 'x1', x1, 1), J$.T(1025, 2, 22, false), J$.R(1033, 'y1', y1, 1), J$.T(1041, 3, 22, false)));
            }
        } catch (J$e) {
            J$.Ex(1273, J$e);
        } finally {
            if (J$.Sr(1281)) {
                J$.L();
                continue jalangiLabel85;
            } else {
                J$.L();
                break jalangiLabel85;
            }
        }
    }
// JALANGI DO NOT INSTRUMENT
