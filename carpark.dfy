// By default, a function is ghost, and cannot be called from non-ghost code.  To make it non-ghost, replace the keyword function with the two keywords “function method”.
// http://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf pg 76

class {:autocontracts} CarPark 
{
    // Log messages
    const debug := true;

    // Total car park size
    const carParkSize:= 20;

    // Minimum number of empty spaces
    const minEmptySpaces:= 5;

    // Number of reserved spaces - 0 by default
    const reservedSpacesSize:= 5;

    // The current number of subscriptions
    var subscriptionCount : int

    // Array of vehicle registrations with subscription
    var subscriptionRegistrations: seq<int>;

    // If reserved parking in force, true by default
    var reservedParkingInForce: bool;
    
    // IDs of public available spaces
    var availableSpaces: set<int>;

    // IDs of reserved spaces
    var reservedSpaces: set<int>;
    
    // IDs of in use spaces
    var inUseSpaces: set<int>;

    // Set car park size
    constructor ()
    // Ensure sets are correct size
    ensures |inUseSpaces| == 0; 
    ensures |reservedSpaces| == reservedSpacesSize;
    ensures |availableSpaces| == carParkSize - reservedSpacesSize;
    ensures subscriptionCount == 0;
    ensures |subscriptionRegistrations| == 0;
    ensures reservedParkingInForce;
    {
        this.subscriptionRegistrations:= [];
        this.subscriptionCount:= 0;
        this.reservedParkingInForce:= true;
        // Hard coding set values as cardinality won't work with set comprehension
        // https://stackoverflow.com/a/48989897/10789835
        this.inUseSpaces:= {};
        this.reservedSpaces:= {0,1,2,3,4};
        this.availableSpaces:= {5,6,7,8,9,10,11,12,13,14,15,16,17,18,19};
    }

    method printSets()
    {
        print "inUseSpaces: ", this.inUseSpaces, "\n";
        print "reservedSpaces: ", this.reservedSpaces, "\n";
        print "availableSpaces: ", this.availableSpaces, "\n";
    }

    method enterCarPark() returns (spaceId: int, success: bool)
    modifies this;
    // If failes:
    // Should be as not enough spaces, and ensure no changes made
    ensures old(|availableSpaces|) <= minEmptySpaces ==> !success;
    ensures !success ==> old(inUseSpaces) == inUseSpaces && old(availableSpaces) == availableSpaces;
    // If success:
    // check spaceId wasn't already in use, and that no other changes made to old set
    ensures success ==> spaceId !in old(inUseSpaces) && old(inUseSpaces) + {spaceId} == inUseSpaces;
    // Check spaceId was available old, and no other changes made to availableSpaces
    ensures success ==> spaceId in old(availableSpaces) && old(availableSpaces) == availableSpaces + {spaceId};
    // Check reserved set not changed regardless
    ensures old(reservedSpaces) == reservedSpaces;
    // autocontract ensures spaceId doesn't exist in more than one set
    {
        // Check if enough empty spaces or return early
        if |availableSpaces| <= minEmptySpaces
        {
            spaceId := -1;
            success := false;
            if debug { print "enterCarPark - availableSpaces less than minEmptySpaces \n"; }
            return;
        }

        // Get an arbitrary id and set success
        spaceId :| spaceId in availableSpaces;
        success := true;

        // Remove spaceId from availableSpaces and add to inUseSpaces
        availableSpaces := availableSpaces - {spaceId};
        inUseSpaces := inUseSpaces + {spaceId};

        if debug { print "enterCarPark - space ", spaceId, "\n"; }

    } 

    method leaveCarPark(spaceId: int) returns (success: bool)
    modifies this;
    // If no success:
    // If spaceId not in old inUse, then should have failed
    ensures spaceId !in old(inUseSpaces) ==> !success;
    // All sets should remain the same
    ensures !success ==> 
        old(inUseSpaces) == inUseSpaces && 
        old(availableSpaces) == availableSpaces && 
        old(reservedSpaces) == reservedSpaces;
    // If success:
    // If success, spaceId should be in old inUseSpaces, but not after and no other changes
    ensures success ==> 
        spaceId in old(inUseSpaces) && 
        spaceId !in inUseSpaces && 
        old(inUseSpaces) == inUseSpaces + {spaceId};
    // If spaceId was reserved space and reservedInForce, spaceId should now be in reservedSpaces with no other changes
    ensures success && reservedParkingInForce && spaceId < reservedSpacesSize ==>
        spaceId !in old(reservedSpaces) &&
        old(reservedSpaces) + {spaceId} == reservedSpaces;
    // If spaceId was not in reserved space, or !reservedParkingInForce, should now be in availableSpaces with no other changes
    ensures success && ((spaceId > reservedSpacesSize) || !reservedParkingInForce) ==> 
        spaceId !in old (availableSpaces) &&
        old(availableSpaces) + {spaceId} == availableSpaces;
    // Precontract enforces correct set length and no duplication
    {
        // If not inUse, fail early
        if (spaceId !in inUseSpaces) 
        {
            success := false;
            if debug { print "leaveCarPark(",spaceId,") - failed, spaceId not in use\n"; }
            return;
        }

        success := true;
        inUseSpaces := inUseSpaces - {spaceId};
        if debug { print "leaveCarPark(",spaceId,") - success\n"; }

        // Check if weekend parking and early return
        if (!reservedParkingInForce)
        {
            availableSpaces := availableSpaces + {spaceId};
            return;
        }

        // Check if space should be returned to reserved parking or not
        if (spaceId < reservedSpacesSize)
        {
            reservedSpaces := reservedSpaces + {spaceId};
        }
        else
        {
            availableSpaces := availableSpaces + {spaceId};
        }
    }

    function checkAvailability(): int
    {
       |availableSpaces| - minEmptySpaces
    }

    // Returns if available spaces greater than minEmptySpaces
    // Needs to be function method to allow use in method body
    function method hasAvailableSpaces(): bool
    {
        |availableSpaces| > minEmptySpaces
    }

    // Return if given reg is subscribed to reserved parking
    // Needs to be function method to allow use in method body
    function method regSubscribed(reg: int): bool
    {
        // Convert array to sequence for ease of checking
        reg in subscriptionRegistrations[..]
    }

    method enterReservedCarPark(registration: int) returns (spaceId: int, success: bool)
    modifies this;
    // If no success in any case, make sure all sets remain unchanged
    ensures !success ==> 
        old(inUseSpaces) == inUseSpaces && 
        old(reservedSpaces) == reservedSpaces && 
        old(availableSpaces) == availableSpaces;
    // If reserved in force:
    // Reject if not a subscriber
    ensures reservedParkingInForce && !regSubscribed(registration) ==> !success;
    // If registered and some reserved spaces available, return success
    ensures reservedParkingInForce && regSubscribed(registration) && |old(reservedSpaces)| > 0 ==> success;
    // Check spaceId was in old(reservedSpaces) but now removed and no other changes
    // Check spaceId wasn't in old(inUseSpaces) but now is with no other changes
    // Check no changes to available spaces
    ensures reservedParkingInForce && success ==> 
        spaceId in old(reservedSpaces) && 
        old(reservedSpaces) - {spaceId} == reservedSpaces &&
        spaceId !in old(inUseSpaces) &&
        old(inUseSpaces) + {spaceId} == inUseSpaces && 
        old(availableSpaces) == availableSpaces;
    // If reserved not in force:
    // If no spaces, should fail - need to check old predicate to check value before set size may be modified
    ensures !reservedParkingInForce && old(!hasAvailableSpaces()) ==> !success;
    ensures !reservedParkingInForce && old(hasAvailableSpaces()) ==> success;
    // Check old(availableSpaces) had spaceId but doesn't now, that inUseSpaces didn't have it but now does and no changes to reserved
    ensures !reservedParkingInForce && success ==> 
        spaceId in old(availableSpaces) &&
        old(availableSpaces) - {spaceId} == availableSpaces &&
        spaceId !in old(inUseSpaces) && 
        inUseSpaces == old(inUseSpaces) + {spaceId} && 
        old(reservedSpaces) == reservedSpaces;
    {
        // Check if registration is allowed (convert array to sequence for easy checking)
        if reservedParkingInForce && !regSubscribed(registration)
        {
            spaceId := -1;
            success := false;
            if debug { print "enterReservedCarPark(",registration,") - reg not subscribed\n"; }
            return;
        }

        // If reserve in force and reg subscribed (need assert |reservedSpaces| > 0 for :| assignment) 
        if reservedParkingInForce && |reservedSpaces| > 0 && regSubscribed(registration)
        {
            spaceId :| spaceId in reservedSpaces;
            reservedSpaces := reservedSpaces - {spaceId};
            inUseSpaces := inUseSpaces + {spaceId};
            success := true;
            if debug { print "enterReservedCarPark(",registration,") - reg in allowed list. Returning spaceID ", spaceId,"\n";}
            return;
        }
        
        
        // If reserved parking not in force but no available space
        if !reservedParkingInForce && !hasAvailableSpaces()
        {
            spaceId := -1;
            success := false;
            if debug { print "enterReservedCarPark(",registration,") - reservedParking not in force but no avail spaces\n";}
            return;
        }

        // If reservedParking not in force and we have available space
        if !reservedParkingInForce && hasAvailableSpaces()
        {
            spaceId :| spaceId in availableSpaces;
            availableSpaces := availableSpaces - {spaceId};
            inUseSpaces := inUseSpaces + {spaceId};
            success := true;
            if debug { print "enterReservedCarPark(",registration,") - reservedParking not in force. Returning spaceID ", spaceId,"\n";}
            return;
        }

        // Shouldn't get here
        spaceId := -1;
        success := false;
        if debug { print "enterReservedCarPark(",registration,") - unknown error - not caught by conditions\n";}
    }

    method makeSubscription(registration: int) returns (success: bool)
    modifies this;
    // Ensure in any case that sets haven't changed
    ensures 
        old(availableSpaces) == availableSpaces && 
        old(inUseSpaces) == inUseSpaces && 
        old(reservedSpaces) == reservedSpaces;
    // If failed, subscriptions should not have changed
    ensures !success ==> 
        old(subscriptionRegistrations) == subscriptionRegistrations &&
        old(subscriptionCount) == subscriptionCount;
    // If no room, should fail
    ensures old(subscriptionCount) >= reservedSpacesSize ==> !success;
    // If already registered, should fail
    ensures registration in old(subscriptionRegistrations[..]) ==> !success;
    // If room in array and unique, should pass
    ensures old(subscriptionCount) < reservedSpacesSize && registration !in old(subscriptionRegistrations[..]) ==> 
        success;
    // If pass, check array updated and counter incremented
    ensures success ==> 
        registration !in old(subscriptionRegistrations[..]) && 
        registration in subscriptionRegistrations[..] && 
        subscriptionCount == old(subscriptionCount) + 1 &&
        old(subscriptionRegistrations[..] + [registration]) == subscriptionRegistrations[..];
    {
        // Check space available
        if subscriptionCount >= reservedSpacesSize
        {
            success := false;
            if debug { print "makeSubscription() - subscriptions full, rejected\n";}
            return;
        }

        // Check reg not already subscribed
        if (registration in subscriptionRegistrations[..])
        {
            success := false;
            if debug { print "makeSubscription() - reg already subscribed, rejected\n";}
            return;
        }

        // Make subscription
        subscriptionRegistrations := subscriptionRegistrations + [registration];
        subscriptionCount := subscriptionCount + 1;
        success := true;
        if debug { print "makeSubscription() - reg ", registration, " subscribed \n";}
        return;
    }

    method openReservedArea()
    modifies this;
    // make sure inUse not modified
    ensures old(inUseSpaces) == inUseSpaces;
    ensures !reservedParkingInForce;
    // availableSpaces size should be total of old(availableSpaces) + old(reservedSpaces)
    ensures |availableSpaces| == old(|availableSpaces|) + old(|reservedSpaces|);
    ensures availableSpaces == old(availableSpaces) + old(reservedSpaces);
    // Check reservedSpaces now empty
    ensures |reservedSpaces| == 0;
    {    
        // Update flag
        reservedParkingInForce := false;

        // Move all reserved spaces to available
        availableSpaces := availableSpaces + reservedSpaces;
        reservedSpaces:= {};
        if debug {print "openReservedArea() - done\n";}
    }

    method closeCarPark() returns (destroyed: int)
    modifies this;
    ensures old(|inUseSpaces|) == destroyed;
    ensures inUseSpaces == {};
    ensures |reservedSpaces| == 5;
    ensures |availableSpaces| == 15;
    ensures reservedParkingInForce;
    {
        destroyed := |inUseSpaces|;
        
        // Reset state
        inUseSpaces := {};
        reservedSpaces := {0,1,2,3,4};
        availableSpaces := {5,6,7,8,9,10,11,12,13,14,15,16,17,18,19};  
        reservedParkingInForce := true;
        if debug { print "closeCarPark() - carpark closed. ", destroyed, " cars destroyed\n"; }
    }

    // For overall car park state
    predicate Valid()
    reads this;
    {
        // Ensure no values appear in both given sets
        availableSpaces * inUseSpaces == {} &&
        reservedSpaces * inUseSpaces == {} &&
        availableSpaces * reservedSpaces == {} &&
        // Ensure total size of sets == overall car park size
        |availableSpaces| + |inUseSpaces| + |reservedSpaces| == carParkSize &&
        // Ensure subscription count always between 0 and array length
        0 <= subscriptionCount <= reservedSpacesSize &&
        // Ensure all values in sets are within 0 to carParkSize(20)
        forall i :: i in (availableSpaces + reservedSpaces + inUseSpaces) ==> 0 <= i < carParkSize
    }


    // Needs setting to read only ??
    method printParkingPlan()
    {
        print "\n\n";

        var i:= 0;
        var rowCount:= 0;
        while i < carParkSize
        {
            if i < 10 
            {
                print "0",i;
            } 
            else
            {
                print "",i;
            }
            

            if i in availableSpaces
            {
                print "A ";
            }
            if i in inUseSpaces
            {
                print "X ";
            }
            if i in reservedSpaces
            {
                print "R ";
            }
            

            if rowCount == 4
            { 
                print "\n";
                rowCount := 0;

            } 
            else 
            {
                rowCount := rowCount + 1;
            }
            i:= i + 1;
            
        }

        print "\nTotal Available: ", |availableSpaces|;
        print "\nTotal Reserved: ", |reservedSpaces|;
        print "\nTotal In Use: ", |inUseSpaces|;
        print "\n\n";
        
    }

    method printSubscribedRegistrations()
    {
        print "Subscribed registrations: ", subscriptionRegistrations, "\n";
    }
}



method Main()
{
    // Initialise and print starting car park
    print "New Car Park\n";
    var cp := new CarPark();
    cp.printParkingPlan();

    // Have 10 cars enter public entrance - should all pass
    print "10 cars entering public entrance - should pass\n";
    var c1, s1 := cp.enterCarPark();
    var c2, s2 := cp.enterCarPark();
    var c3, s3 := cp.enterCarPark();
    var c4, s4 := cp.enterCarPark();
    var c5, s5 := cp.enterCarPark();
    var c6, s6 := cp.enterCarPark();
    var c7, s7 := cp.enterCarPark();
    var c8, s8 := cp.enterCarPark();
    var c9, s9 := cp.enterCarPark();
    var c10, s10 := cp.enterCarPark();
    print "Public car entry successful: ", s1, ", ", s2, ", ", s3, ", ", s4, ", ", s5,
        ", ", s6, ", ", s7, ", ", s8, ", ", s9, ", ", s10, "\n";
    cp.printParkingPlan();

    // Have two more cars attempt entry - should fail as 5 spaces must be kept empty and spaceId -1 returned
    print "Attempting two additional entries to public space - should fail\n";
    var c11, s11 := cp.enterCarPark();
    var c12, s12 := cp.enterCarPark();
    print "Public car entry successful: ", c11, ", ", c12, "\n";
    cp.printParkingPlan();
    
    // Have public car attempt to use reserved entrance to verify entry is rejected and spaceId -1 returned
    print "Attempting public car using reserved entrance when not subscribed\n";
    var c13Reg := 131;
    var c13, s13 := cp.enterReservedCarPark(c13Reg);
    print "Entry to reserved successful: ", s13, "\n";
    cp.printParkingPlan();

    // Subscribe car reg and attept access to subscriber entrance
    print "Registering car as subscriber and attempting reserved access again\n";
    var s13r:= cp.makeSubscription(c13Reg);
    c13, s13 := cp.enterReservedCarPark(c13Reg);
    print "Entry to reserved successful: ", s13, "\n";
    cp.printParkingPlan();

    // Attempt to register same car again - should return false
    print "Attempting another subscription with existing subscriber\n";
    s13r:= cp.makeSubscription(c13Reg);
    print "Subscription successful: ", s13r, "\n";

    // Subscribe five more vehicles - four should be successful, one should fail as not enough spaces
    print "Attempting to subscribe five more vehicles - expect one to fail as insufficent reserved spaces\n";
    var c14Reg, c15Reg, c16Reg, c17Reg, c18Reg := 141, 151, 161, 171, 181;
    var s14r:= cp.makeSubscription(c14Reg);
    var s15r:= cp.makeSubscription(c15Reg);
    var s16r:= cp.makeSubscription(c16Reg);
    var s17r:= cp.makeSubscription(c17Reg);
    var s18r:= cp.makeSubscription(c18Reg);
    print "Subscriptions succeeded: ", s14r, ", ", s15r, ", ", s16r, ", ", s17r, ", ", s18r, "\n";
    cp.printSubscribedRegistrations();

    // Attempt to gain access to subscriber gate for subscribed vehicles
    print "Attempt to gain access to subscriber gate for five vehicles just registered - last one should fail as not subscribed\n";
    var c14, s14 := cp.enterReservedCarPark(c14Reg);
    var c15, s15 := cp.enterReservedCarPark(c15Reg);
    var c16, s16 := cp.enterReservedCarPark(c16Reg);
    var c17, s17 := cp.enterReservedCarPark(c17Reg);
    var c18, s18 := cp.enterReservedCarPark(c18Reg);
    print "Reserved entry succeeded: ", s14, ", ", s15, ", ", s16, ", ", s17, ", ", s18, "\n";
    cp.printParkingPlan();

    // Subscribed usets to leave - should return true and restore space to reserved counter
    print "Two subscribers to leave car park, should restore spaces to reserved count\n";
    var c13L := cp.leaveCarPark(c13);
    var c14L := cp.leaveCarPark(c14);
    print "Subscribed cars left successful: ", c13L, ", ", c14L, "\n";
    cp.printParkingPlan();

    // Public users to leave - should return true and restore spaces to available counter
    print "Two public cars to leave car park, should restore spaces to available count\n";
    var c1L := cp.leaveCarPark(c1);
    var c2L := cp.leaveCarPark(c2);
    print "Public car left successful: ", c1L, ", ", c2L, "\n";
    cp.printParkingPlan();

    // Empty space to attempt to leave car park - should return false as not in use
    print "Already empty space to attempt to leave - should return false as invalid request\n";
    c1L := cp.leaveCarPark(c1);
    print "Invalid car left successful: ", c1L, "\n";
    cp.printParkingPlan();

    // Close car park for the night - all cars to be destroyed and car park return to initial state
    print "Car park to close - all remaining cars to be destroyed and car park returned to initial state\n";
    var destroyed := cp.closeCarPark();
    print "Cars destroyed: ", destroyed, "\n";
    cp.printParkingPlan();

    // Set weekend - all cars can use reserved parking
    print "Set weekend parking - all spaces become available\n";
    cp.openReservedArea();
    cp.printParkingPlan();

    // Public car to attempt entry to reserved entrance
    print "Public car to attempt access by reserved entrance\n";
    var c1Reg := 011;
    c1, s1 := cp.enterReservedCarPark(c1Reg);
    print "Public car entry to reserved area successful: ", s1, "\n";
    cp.printParkingPlan();

    // Public car to attempt entry to reserved entrance
    print "Public car to attempt access by public entrance\n";
    c2, s2 := cp.enterCarPark();
    print "Public car entry to public area successful: ", s2, "\n";
    cp.printParkingPlan();

    // Subscribed usets to leave - should return true and restore space to reserved counter
    print "Both cars to leave car park, should restore spaces to available count\n";
    c1L := cp.leaveCarPark(c1);
    c2L := cp.leaveCarPark(c2);
    print "Subscribed cars left successful: ", c1L, ", ", c2L, "\n";
    cp.printParkingPlan();

    // Attempt to have 16 cars enter the car park - last one should fail as min 5 empty spaces required
    print "Attempting 16 cars entry to carpark - last should fail as min 5 empty spaces required\n";
    print "Public car entry successfull: ";
    var x:= 0;
    while x < 16
    {
        var cx, rx := cp.enterCarPark();
        print rx, ", ";
        x := x + 1;
    }
    print "\n";
}