/* global J$ */

var USER_RE = /^.{1,20}$/;
var FNAME_RE = /^.{1,100}$/;
var LNAME_RE = /^.{1,100}$/;
var EMAIL_RE = /^[\S]+@[\S]+\.[\S]+$/;
var PASS_RE =/^(?=.*\d)(?=.*[a-z])(?=.*[A-Z]).{8,}$/;

var userName = J$.readString();
var firstName = J$.readString();
var lastName = J$.readString();
var password = J$.readString();
var verify = J$.readString();
var email = J$.readString();

var all_checks = true;

if (!USER_RE.test(userName)) {
  console.log("Invalid user name.");
  all_checks = false;
}
if (!FNAME_RE.test(firstName)) {
  console.log("Invalid first name.");
  all_checks = false;
}

if (!LNAME_RE.test(lastName)) {
  console.log("Invalid last name.");
  all_checks = false;
}
if (!PASS_RE.test(password)) {
  console.log("Password must be 8 to 18 characters including numbers, lowercase and uppercase letters.");
  all_checks = false;
}
if (password !== verify) {
  console.log("Password must match");
  all_checks = false;
}
if (!EMAIL_RE.test(email)) {
  console.log("Invalid email address");
  all_checks = false; // FIXME: Added this.
}

if (all_checks) {
  console.log("Success!");
}
