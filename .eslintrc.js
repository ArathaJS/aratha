module.exports = {
    "root": true,
    "parserOptions": {
        "ecmaVersion": "2017"
    },
    "env": {
        "browser": true,
        "commonjs": true,
        "es6": true,
        "node": true
    },
    "extends": "eslint:recommended",
    "rules": {
        "indent": [
            "error",
            4,
            {
                "SwitchCase": 1
            }
        ],
        "linebreak-style": [
            "error",
            "unix"
        ],
        "no-console": "off",
        "no-use-before-define": "error",
        "no-var": "error",
        "prefer-const": "error",
        "quotes": [
            "error",
            "double",
            {
                "avoidEscape": true,
            }
        ],
        "semi": [
            "error",
            "always"
        ]
    }
};
