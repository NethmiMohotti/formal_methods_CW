/* Spaceship
* Author: Nethmi Mohotti
* Creation date: 12/20/2023
*/
MACHINE
    Spaceship
    
SETS
    //game status messages
    GAME_STATUS = { Game_Won, Game_Lost, Game_not_over};
    
    // Movement types of spaceship
    MOVEMENT_TYPE = {Move_Up, Move_Down, Move_Right, Move_Left, Warp_Drive};
    
    
    //report messages for the game
    GAME_REPORT = {New_game_started,Game_Win, Lost_Game, Successfully_moved_up, Successfully_moved_down, Successfully_moved_right, Successfully_moved_left, Warp_drive_successful, Scapceship_collided_with_Asteroid, No_power_after_collision, Spaceship_out_of_space, No_power_for_the_move, Warp_drive_to_the_current_location, Unable_to_wrap_to_StartBase}
    
    
CONSTANTS
    xRegion, yRegion, 
    Space,  FreeSpace, AteroidLocation, StarBase,  HomeBase,
    NormalMovePower, WarpDrivePower, CollisionPowerLoss
    
PROPERTIES
    xRegion <: NAT1 & xRegion = 1..12 &
    yRegion <: NAT1 & yRegion = 1..7 &
    
    //valid space
    Space = xRegion * yRegion &
    
    //Asteroid location 
    AteroidLocation <: Space &
    AteroidLocation = {(3 |-> 2), (3 |-> 5), (5 |-> 4), (6 |-> 7), (7 |-> 1), 
        (7 |-> 5), (7 |-> 7), (8 |-> 3), (10 |-> 6), (11 |-> 2), (12 |-> 5) } &
    
    
    //boundary of the space
    //FreeSpace = {xx,yy | xx:NAT1 & yy:NAT1 & xx<=12 & yy <=7} &
    FreeSpace <: Space & 
    FreeSpace /\ AteroidLocation = {} &
    FreeSpace \/ AteroidLocation = Space &
    
    //star base location
    StarBase : Space &
    StarBase = 6 |-> 4 &
    
    //start location
    HomeBase : FreeSpace &
    HomeBase = 1|->1 &
    
    //power consumption volume
    NormalMovePower = 5 &
    WarpDrivePower = 20 &
    CollisionPowerLoss = 10
    
    
DEFINITIONS
    //check whether the game is over by checking Spaceship is in the Star-base position or low power required
    isGameOver == (xPosition |-> yPosition = StarBase) or (spaceshipPower < NormalMovePower);
    
    //check for the collision of the asteroids
    didAsteroidCollide(xCordinate, yCordinate) == (xCordinate |-> yCordinate : AteroidLocation);
    
    //check if the Spaceship is moving within the space
    spaceshipInSpace(xCordinate, yCordinate) == (xCordinate |-> yCordinate : Space);
    
    //check if the power of the Spaceship is enough for the moves
    powerCheck(currentPower, movePower) == (currentPower > movePower)
    
    
    //check if the spaceship is docked at Star-Base
    //isDocked (xPosition |-> yPosition = StarBase)
    
    
VARIABLES
    xPosition,      //current X position
    yPosition,      //current Y position
    spaceshipPower, //power of the spaceship have
    movements,      //movements of the spaceship
    missionRoute,   //the regions visited by the spaceship
    collisionCount, //store the collisions spaceship had
    currentPosition,//current position of the spaceship
    gameState       //to store the status of the game
    
INVARIANT
    xPosition : xRegion &
    yPosition : yRegion &
    xPosition |-> yPosition : Space &
    spaceshipPower : NAT &
    collisionCount : NAT &
    movements : seq(MOVEMENT_TYPE) &
    missionRoute : seq(FreeSpace) & 
    currentPosition : FreeSpace &
    gameState <: GAME_STATUS
    
INITIALISATION
    xPosition := prj1(xRegion,yRegion)(HomeBase)  ||
    yPosition := prj2(xRegion,yRegion)(HomeBase) ||
    spaceshipPower := 0 ||
    collisionCount := 0 ||
    movements := [] ||
    missionRoute := [HomeBase] ||
    currentPosition := HomeBase ||
    gameState := {}
    
OPERATIONS
//****************************************************************************************************//    
//New game operation: request a power value to the operation & restart the game with initial values
    startNew <-- NewGame(power) =
    PRE 
        power : NAT1 & power mod 20 = 0 & power < 200
    THEN
        xPosition := 1 ||
        yPosition := 1 ||
        spaceshipPower := power ||
        collisionCount := 0 ||
        movements := [] ||
        missionRoute := [HomeBase] ||
        currentPosition := HomeBase ||
        gameState := {Game_not_over} ||
        startNew := New_game_started
    END;
    
    
//****************************************************************************************************//   
//display spaceship information: current position, current power, and no. of collisions
    spaceshiCurrentPosition, spaceshipCurrentPower, spaceshipCollisionCount <-- MissionInformation =
    BEGIN
        spaceshiCurrentPosition := currentPosition ||
        spaceshipCurrentPower := spaceshipPower ||
        spaceshipCollisionCount := collisionCount
    END;

//****************************************************************************************************//   
//display the route of the mission
    route <-- RegionsVisited =
    BEGIN
        route := missionRoute
    END;


//****************************************************************************************************//   
//display the status of the mission
    status <-- GameStatus =
    PRE
        status : GAME_STATUS & not(currentPosition = HomeBase)
    THEN
        IF(currentPosition = StarBase)
        THEN
            status := Game_Won
        ELSIF (spaceshipPower < NormalMovePower)
        THEN
            status := Game_Lost
        ELSE
            status := Game_not_over
        END
    END;
    
//****************************************************************************************************//       
//spaceship move up operation
    upMessage <-- MoveUp =
    PRE        
        not(isGameOver) //operation available only if the game is not over
    THEN
        IF 
            powerCheck(spaceshipPower, NormalMovePower) //check if the Spaceship power is sufficient for the move
        THEN
            IF
                spaceshipInSpace (xPosition, succ(yPosition))  //check if the position to move is in the space
            THEN
                IF 
                    didAsteroidCollide(xPosition, succ(yPosition)) //check if the new position contain an asteroid
                THEN
                    collisionCount := succ(collisionCount) ||
                    IF (spaceshipPower - CollisionPowerLoss > 0)
                    THEN 
                        //spaceship collided with Asteroid
                        spaceshipPower := spaceshipPower - CollisionPowerLoss ||
                        upMessage := Scapceship_collided_with_Asteroid ||
                        currentPosition := (xPosition |-> yPosition) ||
                        gameState := {Game_not_over}
                    ELSE
                        spaceshipPower := 0 ||  //no power after the collision
                        upMessage := No_power_after_collision ||
                        gameState := {Game_Lost}
                    END 
                ELSIF 
                    (xPosition |-> yPosition+1 = StarBase)
                THEN 
                    yPosition := succ(yPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(xPosition |-> succ(yPosition))||
                    currentPosition := (xPosition |-> succ(yPosition)) ||                  
                    movements := movements <- Move_Up ||
                    upMessage := Game_Win ||
                    gameState := {Game_Won} 
                    
                ELSE
                    yPosition := succ(yPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(xPosition |-> succ(yPosition))||
                    currentPosition := (xPosition |-> succ(yPosition)) ||                  
                    movements := movements <- Move_Up ||
                    upMessage := Successfully_moved_up ||
                    gameState := {Game_not_over}                    
                END                
            ELSE
                upMessage := Spaceship_out_of_space
                
            END
        ELSE
            upMessage := No_power_for_the_move || gameState := {Game_Lost}      
        END     
    END;


//****************************************************************************************************//       
//spaceship move right operation
    rightMassage <-- MoveRight =
    PRE
        not(isGameOver) //operation available only if the game is not over
    THEN
        IF 
            powerCheck(spaceshipPower, NormalMovePower) //check if the Spaceship power is sufficient for the move
        THEN
            IF
                spaceshipInSpace (succ(xPosition), yPosition) //check if the position to move is in the space
            THEN
                IF 
                    didAsteroidCollide(succ(xPosition), yPosition)  //check if the new position contain an asteroid
                THEN
                    collisionCount := succ(collisionCount) ||
                    IF (spaceshipPower - CollisionPowerLoss > 0)
                    THEN 
                        //spaceship collided with Asteroid
                        spaceshipPower := spaceshipPower - CollisionPowerLoss ||
                        rightMassage := Scapceship_collided_with_Asteroid ||
                        currentPosition := (xPosition |-> yPosition) ||
                        gameState := {Game_not_over}
                    ELSE
                        spaceshipPower := 0 ||  //no power after the collision
                        rightMassage := No_power_after_collision ||
                        gameState := {Game_Lost}
                    END 
                ELSIF 
                    (xPosition |-> yPosition+1 = StarBase)
                THEN 
                    xPosition := succ(xPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(succ(xPosition) |-> yPosition)||
                    currentPosition := (succ(xPosition) |-> yPosition) ||
                    movements := movements <- Move_Right ||
                    rightMassage := Game_Win ||
                    gameState := {Game_Won}                    
                ELSE
                    xPosition := succ(xPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(succ(xPosition) |-> yPosition)||
                    currentPosition := (succ(xPosition) |-> yPosition) ||                  
                    movements := movements <- Move_Right ||
                    rightMassage := Successfully_moved_right ||
                    gameState := {Game_not_over}                    
                END                
            ELSE
                rightMassage := Spaceship_out_of_space                
            END
        ELSE
            rightMassage := No_power_for_the_move ||
            gameState := {Game_Lost}      
        END
    END;
    
//****************************************************************************************************//       
//spaceship move down operation
    downMessage <-- MoveDown =
    PRE
        not(isGameOver) //operation available only if the game is not over
    THEN
        IF 
            powerCheck(spaceshipPower, NormalMovePower) //check if the Spaceship power is sufficient for the move
        THEN
            IF
                spaceshipInSpace (xPosition, pred(yPosition)) //check if the position to move is in the space
            THEN
                IF 
                    didAsteroidCollide(xPosition, pred(yPosition)) //check if the new position contain an asteroid
                THEN
                    collisionCount := pred(collisionCount) ||
                    IF (spaceshipPower - CollisionPowerLoss > 0)
                    THEN 
                        //spaceship collided with Asteroid
                        spaceshipPower := spaceshipPower - CollisionPowerLoss ||
                        downMessage := Scapceship_collided_with_Asteroid ||
                        currentPosition := (xPosition |-> yPosition) ||
                        gameState := {Game_not_over}
                    ELSE
                        spaceshipPower := 0 ||  //no power after the collision
                        downMessage := No_power_after_collision ||
                        gameState := {Game_Lost}
                    END 
                ELSIF 
                    (xPosition |-> yPosition+1 = StarBase)
                THEN 
                    yPosition := pred(yPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(xPosition |-> pred(yPosition))||
                    currentPosition := (xPosition |-> pred(yPosition)) ||
                    movements := movements <- Move_Down ||
                    downMessage := Game_Win ||
                    gameState := {Game_Won}                    
                ELSE
                    yPosition := pred(yPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(xPosition |-> pred(yPosition))||
                    currentPosition := (xPosition |-> pred(yPosition)) ||                  
                    downMessage := Successfully_moved_down ||
                    movements := movements <- Move_Down ||
                    gameState := {Game_not_over}                    
                END                
            ELSE
                downMessage := Spaceship_out_of_space                
            END
        ELSE
            downMessage := No_power_for_the_move ||
            gameState := {Game_Lost}      
        END     
    END;


//****************************************************************************************************//   
//spaceship move left operation
    leftMassage <-- MoveLeft=
    PRE
        not(isGameOver) //operation available only if the game is not over
    THEN
        IF 
            powerCheck(spaceshipPower, NormalMovePower) //check if the Spaceship power is sufficient for the move
        THEN
            IF
                spaceshipInSpace (pred(xPosition), yPosition) //check if the position to move is in the space
            THEN
                IF 
                    didAsteroidCollide(pred(xPosition), yPosition)  //check if the new position contain an asteroid
                THEN
                    collisionCount := pred(collisionCount) ||
                    IF (spaceshipPower - CollisionPowerLoss > 0)
                    THEN 
                        //spaceship collided with Asteroid
                        spaceshipPower := spaceshipPower - CollisionPowerLoss ||
                        leftMassage := Scapceship_collided_with_Asteroid ||
                        currentPosition := (xPosition |-> yPosition) ||                     
                        gameState := {Game_not_over}
                    ELSE
                        spaceshipPower := 0 ||  //no power after the collision
                        leftMassage := No_power_after_collision ||
                        gameState := {Game_Lost}
                    END 
                ELSIF 
                    (xPosition |-> yPosition+1 = StarBase)
                THEN 
                    xPosition := pred(xPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(pred(xPosition) |-> yPosition)||
                    currentPosition := (pred(xPosition) |-> yPosition) ||
                    movements := movements <- Move_Left ||
                    leftMassage := Game_Win ||
                    gameState := {Game_Won}                    
                ELSE
                    xPosition := pred(xPosition) ||
                    spaceshipPower := spaceshipPower - NormalMovePower ||                    
                    missionRoute:= missionRoute <-(pred(xPosition) |-> yPosition)||
                    currentPosition := (pred(xPosition) |-> yPosition) ||
                    movements := movements <- Move_Left ||
                    leftMassage := Successfully_moved_left ||
                    gameState := {Game_not_over}                    
                END                
            ELSE
                leftMassage := Spaceship_out_of_space                
            END
        ELSE
            leftMassage := No_power_for_the_move ||
            gameState := {Game_Lost}      
        END
    END;
    
    
//****************************************************************************************************//       
//Warp drive operation
    driveMessage <-- WarpDrive (newPositionX , newPositionY) =
    PRE
        newPositionX: NAT1 & newPositionY: NAT1 & not(isGameOver)
    THEN
        IF 
            powerCheck(spaceshipPower, WarpDrivePower) //check if the Spaceship power is sufficient for the move
        THEN
            IF
                spaceshipInSpace (newPositionX, newPositionY) //check if the position to move is in the space
            THEN                
                IF 
                    didAsteroidCollide(newPositionX, newPositionY)  //check if the new position contain an asteroid
                THEN
                    collisionCount := pred(collisionCount) ||
                    IF (spaceshipPower - CollisionPowerLoss > 0)
                    THEN 
                        //spaceship collided with Asteroid
                        spaceshipPower := spaceshipPower - CollisionPowerLoss ||
                        driveMessage := Scapceship_collided_with_Asteroid ||
                        currentPosition := (xPosition |-> yPosition) ||                     
                        gameState := {Game_not_over}
                    ELSE
                        spaceshipPower := 0 ||  //no power after the collision
                        driveMessage := No_power_after_collision ||
                        gameState := {Game_Lost}
                    END
                    
                ELSIF
                    (newPositionX = xPosition & newPositionY = yPosition)
                THEN                    
                    driveMessage := Warp_drive_to_the_current_location ||
                    spaceshipPower := spaceshipPower - WarpDrivePower ||                    
                    currentPosition := (xPosition |-> yPosition) ||                     
                    gameState := {Game_not_over}
                ELSIF 
                    (newPositionX |-> newPositionX = StarBase)
                THEN 
                    driveMessage := Unable_to_wrap_to_StartBase ||
                    spaceshipPower := spaceshipPower - WarpDrivePower ||                    
                    currentPosition := (xPosition |-> yPosition) ||                     
                    gameState := {Game_not_over}
                ELSE
                    xPosition,yPosition  := newPositionX,newPositionY  ||
                    missionRoute:= missionRoute <-(newPositionX |-> newPositionY)||
                    currentPosition := (newPositionX |-> newPositionY) ||
                    movements := movements <- Warp_Drive ||
                    spaceshipPower := spaceshipPower - WarpDrivePower ||                    
                    driveMessage := Warp_drive_successful ||
                    gameState := {Game_not_over}   
                END
            ELSE
                driveMessage := Spaceship_out_of_space                
            END
        ELSE
            driveMessage := No_power_for_the_move ||
            gameState := {Game_Lost}      
        END       
    END
END
